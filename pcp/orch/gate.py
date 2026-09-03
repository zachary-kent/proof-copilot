"""The integrity gate: deterministic, model-free (PLAN.md 8.7).

A pure function of (frozen store, worker patch), run in a scratch directory.  No
model is involved at any point -- not to check the proof, and above all not to review
a success: the kernel already did that, and "no model ever reviews a success" is one
of the three economics rules the whole design rests on.

An agent-built development can be fully `Qed`-clean and still worthless, because the
kernel checks *proofs*, not *statements*.  Every check here exists because of a
specific way that goes wrong.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable

from pcp.core.vernac import parse_blocks
from pcp.orch.assemble import PROOF_USING_DIRECTIVE, Assembly, Development, NodeSpec

#: Axioms Rocq/Iris developments legitimately rest on.  Anything else is an event.
DEFAULT_AXIOM_WHITELIST = (
    "functional_extensionality_dep",
    "propositional_extensionality",
    "proof_irrelevance",
    "Classical_Prop.classic",
    "ClassicalEpsilon.constructive_indefinite_description",
    "Eqdep.Eq_rect_eq.eq_rect_eq",
    "JMeq_eq",
)

#: Things a worker must never introduce in a proof body.
_FORBIDDEN_BODY = (
    (re.compile(r"\badmit\b"), "admit"),
    (re.compile(r"\bAdmitted\b"), "Admitted"),
    (re.compile(r"\bAxiom\b"), "Axiom"),
    (re.compile(r"\bParameter\b"), "Parameter"),
    (re.compile(r"\bConjecture\b"), "Conjecture"),
    (re.compile(r"\bgive_up\b"), "give_up"),
)

#: Escape hatches that turn the kernel off.  These are not style issues.
_ESCAPE_HATCHES = (
    (re.compile(r"Unset\s+Universe\s+Checking"), "Unset Universe Checking"),
    (re.compile(r"Unset\s+Guard\s+Checking"), "Unset Guard Checking"),
    (re.compile(r"Unset\s+Positivity\s+Checking"), "Unset Positivity Checking"),
    (re.compile(r"Obligation\s+Tactic\s*:="), "Obligation Tactic override"),
    (re.compile(r"#\[\s*bypass_check"), "bypass_check attribute"),
    (re.compile(r"Unset\s+Elimination\s+Schemes"), "Unset Elimination Schemes"),
)

#: Global registrations change how *future* statements elaborate, which is a
#: statement-meaning attack surface.  Node-local versions are fine.
_GLOBAL_AMBIENT = (
    (re.compile(r"^\s*(?:Global\s+)?Instance\b", re.M), "Instance (use `Local Instance`)"),
    (re.compile(r"^\s*#\[\s*global\s*\]", re.M), "#[global] attribute"),
    (re.compile(r"^\s*(?:Global\s+)?Hint\b", re.M), "Hint (use `Local Hint`)"),
    (re.compile(r"^\s*Notation\b", re.M), "Notation"),
    (re.compile(r"^\s*(?:Global\s+)?Ltac\b", re.M), "Ltac (use `Local Ltac`)"),
    (re.compile(r"^\s*Canonical\b", re.M), "Canonical Structure"),
    (re.compile(r"^\s*Coercion\b", re.M), "Coercion"),
)

_ASSUMPTION_LINE = re.compile(r"^\s{0,4}(\S+)\s*:", re.M)


@dataclass
class Check:
    name: str
    ok: bool
    detail: str = ""
    #: Advisory checks report but do not fail the gate.
    advisory: bool = False

    def render(self) -> str:
        mark = "ok " if self.ok else ("warn" if self.advisory else "FAIL")
        line = f"  [{mark}] {self.name}"
        if self.detail:
            line += f": {self.detail}"
        return line


@dataclass
class GateResult:
    ok: bool
    checks: list[Check] = field(default_factory=list)
    assumptions: dict[str, list[str]] = field(default_factory=dict)
    compile_output: str = ""
    elapsed_s: float = 0.0
    assembled: str = ""
    unused_premises: list[str] = field(default_factory=list)

    @property
    def failures(self) -> list[Check]:
        return [c for c in self.checks if not c.ok and not c.advisory]

    def render(self) -> str:
        head = "gate: PASS" if self.ok else "gate: FAIL"
        lines = [f"{head} ({self.elapsed_s:.1f}s)"]
        lines += [c.render() for c in self.checks]
        if not self.ok and self.compile_output:
            lines.append("")
            lines.append(_tail(self.compile_output, 40))
        return "\n".join(lines)

    def to_json(self) -> dict[str, Any]:
        return {
            "ok": self.ok,
            "elapsed_s": self.elapsed_s,
            "checks": [{"name": c.name, "ok": c.ok, "detail": c.detail, "advisory": c.advisory} for c in self.checks],
            "assumptions": self.assumptions,
            "unused_premises": self.unused_premises,
        }


def _tail(text: str, n: int) -> str:
    lines = text.strip().splitlines()
    return "\n".join(lines[-n:])


# --------------------------------------------------------------------------- coqc

def coq_project_flags(root: Path) -> list[str]:
    """Read ``_CoqProject`` for the load-path flags, ignoring file lists."""
    path = root / "_CoqProject"
    if not path.exists():
        return []
    flags: list[str] = []
    tokens = path.read_text(encoding="utf-8").split()
    i = 0
    while i < len(tokens):
        tok = tokens[i]
        if tok in ("-Q", "-R"):
            flags += tokens[i : i + 3]
            i += 3
        elif tok == "-I":
            flags += tokens[i : i + 2]
            i += 2
        elif tok == "-arg":
            flags.append(tokens[i + 1])
            i += 2
        else:
            i += 1
    return flags


def coqc_binary() -> str | None:
    return os.environ.get("PCP_COQC") or shutil.which("coqc") or shutil.which("rocq")


class Gate:
    """Runs the deterministic checks.  Reusable across nodes; holds no state."""

    def __init__(
        self,
        development: Development,
        *,
        workdir: Path | None = None,
        axiom_whitelist: Iterable[str] = DEFAULT_AXIOM_WHITELIST,
        timeout: float = 600.0,
        extra_flags: Iterable[str] = (),
    ) -> None:
        self.dev = development
        self.root = development.path.parent
        self.workdir = workdir
        self.whitelist = set(axiom_whitelist)
        self.timeout = timeout
        self.flags = list(coq_project_flags(self.root)) + list(extra_flags)
        self.last_stdout = ""
        self.last_stderr = ""

    # -- the cheap half, run before anything is compiled -------------------
    def static_checks(self, bodies: dict[str, str]) -> list[Check]:
        """Everything that can be decided by reading the patch.

        Deterministic before model, and cheap before expensive: a body carrying an
        `admit` is rejected without paying for a Rocq compile.
        """
        checks: list[Check] = []

        offenders = [
            f"{node}: {label}"
            for node, body in bodies.items()
            for pattern, label in _FORBIDDEN_BODY
            if pattern.search(_strip_comments(body))
        ]
        checks.append(
            Check(
                "no new Admitted / admit / Axiom / Parameter",
                not offenders,
                "; ".join(offenders),
            )
        )

        hatches = [
            f"{node}: {label}"
            for node, body in bodies.items()
            for pattern, label in _ESCAPE_HATCHES
            if pattern.search(_strip_comments(body))
        ]
        checks.append(Check("no escape hatches", not hatches, "; ".join(hatches)))

        ambient = [
            f"{node}: {label}"
            for node, body in bodies.items()
            for pattern, label in _GLOBAL_AMBIENT
            if pattern.search(_strip_comments(body))
        ]
        checks.append(
            Check(
                "ambient-state hygiene (no global Instance/Hint/Notation/Ltac)",
                not ambient,
                "; ".join(ambient),
            )
        )
        return checks

    # -- the whole gate ----------------------------------------------------
    def run(
        self,
        anchor: str,
        nodes: list[NodeSpec],
        *,
        target_body: str | None = None,
        target: str | None = None,
        truncate: bool = True,
        check_assumptions: bool = True,
        extra_preamble: str = "",
        unused_premise_report: bool = False,
        stub_prefix: bool = False,
    ) -> GateResult:
        """Gate one node.

        Sibling nodes still stubbed with ``Admitted`` are legitimate assumptions for
        a *per-node* gate -- that is the entire content of Claim 1, and refusing them
        would serialise the frontier.  Integration (``truncate=False`` over a fully
        proved set) is where the whitelist bites, because then there are no stubs.
        """
        started = time.perf_counter()
        target = target or anchor
        bodies = {spec.name: spec.body for spec in nodes if spec.body}
        if target_body:
            bodies[anchor] = target_body

        checks = self.static_checks({k: v for k, v in bodies.items() if v})

        proved = [spec.name for spec in nodes if spec.body] + ([anchor] if target_body else [])
        # Sibling obligations still stubbed are legitimate assumptions for a per-node
        # gate; so is the anchor itself when we are checking a child against it.
        stubs = {spec.name for spec in nodes if spec.body is None}
        if target_body is None:
            stubs.add(anchor)
        trailer = ""
        if check_assumptions and proved:
            trailer = "\n".join(f"Print Assumptions {name}." for name in proved)

        assembly = self.dev.assemble(
            anchor,
            nodes,
            anchor_body=target_body,
            truncate=truncate,
            extra_preamble=extra_preamble,
            trailer=trailer,
            stub_prefix=stub_prefix,
        )
        stubs |= set(assembly.stubbed)

        # Item 2: the statement is byte-identical by construction.  Assert it anyway
        # -- this is the check the whole freeze rests on, and a silent regression in
        # span arithmetic would be invisible everywhere else.
        pinned = _statement_present(assembly.text, target, self.dev, nodes)
        checks.append(
            Check(
                "statement pinning by construction",
                pinned,
                "" if pinned else "the frozen statement text is not present verbatim in the assembly",
            )
        )
        checks.append(
            Check(
                "`Proof using` discipline",
                PROOF_USING_DIRECTIVE in assembly.text,
                "" if PROOF_USING_DIRECTIVE in assembly.text else "missing Set Default Proof Using",
            )
        )

        result = GateResult(ok=False, checks=checks, assembled=assembly.text)

        if any(not c.ok and not c.advisory for c in checks):
            # Do not pay for a compile when the patch is already disqualified.
            result.elapsed_s = time.perf_counter() - started
            result.checks.append(Check("compiles (coqc)", False, "skipped: static checks failed"))
            return result

        compiled, output = self._compile(assembly)
        result.compile_output = output
        checks.append(Check("compiles (coqc)", compiled, "" if compiled else _first_error(output)))

        if compiled and check_assumptions:
            result.assumptions = parse_assumptions(self.last_stdout, proved)
            allowed = self.whitelist | stubs
            bad = {
                name: [a for a in axioms if a not in allowed]
                for name, axioms in result.assumptions.items()
            }
            bad = {k: v for k, v in bad.items() if v}
            detail = "; ".join(f"{k}: {', '.join(v)}" for k, v in bad.items())
            if not result.assumptions and proved:
                detail = "could not read Print Assumptions output; treat as unverified"
            checks.append(
                Check(
                    "axiom hygiene (Print Assumptions ⊆ whitelist + open stubs)",
                    not bad and bool(result.assumptions or not proved),
                    detail,
                )
            )
            leaning = sorted({a for axioms in result.assumptions.values() for a in axioms if a in stubs})
            if leaning:
                checks.append(
                    Check(
                        "rests on open stubs",
                        True,
                        ", ".join(leaning) + " (expected until they are discharged)",
                        advisory=True,
                    )
                )

        if compiled and unused_premise_report and target_body:
            unused, note = self.deep_unused_premises(anchor, nodes, target_body, extra_preamble)
            result.unused_premises = unused
            checks.append(
                Check(
                    "unused-premise report",
                    not unused,
                    ("the proof does not need: " + ", ".join(unused)) if unused else note,
                    advisory=True,
                )
            )

        result.ok = all(c.ok or c.advisory for c in checks)
        result.elapsed_s = time.perf_counter() - started
        return result

    def deep_unused_premises(
        self,
        anchor: str,
        nodes: list[NodeSpec],
        target_body: str,
        extra_preamble: str = "",
        *,
        max_probes: int = 8,
    ) -> tuple[list[str], str]:
        """Premises this proof does not need -- by removal probe, not by inspection.

        The obvious implementation (print the proof term, look for the binder) is
        *unsound*: `Qed` is opaque, and even with `Defined` the printer elides
        implicit arguments, so a premise that is used can look absent.  Reporting a
        used premise as unused would send the operator to weaken a statement that is
        exactly right, so this asks the kernel instead: restate the lemma without the
        premise and re-run the same proof.  If it still compiles, the premise was
        unnecessary.  That is ground truth, at one compile per candidate.

        Bounded and opt-in: explicit `(x : T)` binders only, at most ``max_probes`` of
        them.  Everything it compiles lives in a scratch directory and is discarded --
        no amended statement ever reaches the development.
        """
        from pcp.orch.assemble import remove_binder, statement_binders

        block = self.dev.block(anchor)
        if block is None:
            return [], "no such declaration"
        candidates = statement_binders(block.statement)
        if not candidates:
            return [], "no explicit binders to probe"
        if len(candidates) > max_probes:
            return [], f"{len(candidates)} binders exceeds the probe budget of {max_probes}"

        unused: list[str] = []
        for name in candidates:
            weaker = remove_binder(block.statement, name)
            if weaker is None:
                continue
            assembly = self.dev.assemble(
                anchor,
                nodes,
                anchor_body=target_body,
                truncate=True,
                extra_preamble=extra_preamble,
                statement_override=weaker,
            )
            ok, _ = self._compile(assembly)
            if ok:
                unused.append(name)
        return unused, ""

    def run_design(
        self,
        candidate: str,
        contract,
        *,
        proved: list[str] | None = None,
        check_assumptions: bool = True,
    ) -> GateResult:
        """Gate a whole-file submission for a design task.

        The submitter supplies definitions *and* proofs; what it may not supply is a
        different program, a different specification, or a change to anything the
        contract did not declare mutable.  ``proved`` defaults to every lemma the
        candidate closes with `Qed`.
        """
        started = time.perf_counter()
        bodies = {
            b.name: b.body(candidate)
            for b in parse_blocks(candidate)
            if b.has_proof and b.ender in ("Qed", "Defined")
        }
        if proved is None:
            proved = [
                b.name for b in parse_blocks(candidate)
                if b.has_proof and b.ender == "Qed"
            ]
        checks = self.static_checks(bodies)
        checks.append(contract.check(self.dev.source, candidate))

        result = GateResult(ok=False, checks=checks, assembled=candidate)
        if any(not c.ok and not c.advisory for c in checks):
            result.elapsed_s = time.perf_counter() - started
            result.checks.append(Check("compiles (coqc)", False, "skipped: static checks failed"))
            return result

        text = candidate
        if check_assumptions and proved:
            text = candidate.rstrip() + "\n\n" + "\n".join(f"Print Assumptions {n}." for n in proved) + "\n"
        compiled, output = self._compile(Assembly(text=text))
        result.compile_output = output
        checks.append(Check("compiles (coqc)", compiled, "" if compiled else _first_error(output)))
        if compiled and check_assumptions and proved:
            result.assumptions = parse_assumptions(self.last_stdout, proved)
            bad = {
                n: [a for a in ax if a not in self.whitelist]
                for n, ax in result.assumptions.items()
            }
            bad = {k: v for k, v in bad.items() if v}
            checks.append(
                Check(
                    "axiom hygiene (Print Assumptions ⊆ whitelist)",
                    not bad,
                    "; ".join(f"{k}: {', '.join(v)}" for k, v in bad.items()),
                )
            )
        result.ok = all(c.ok or c.advisory for c in checks)
        result.elapsed_s = time.perf_counter() - started
        return result

    def _compile(self, assembly: Assembly) -> tuple[bool, str]:
        coqc = coqc_binary()
        if coqc is None:
            return False, "no coqc on PATH -- run ./scripts/setup-toolchain.sh and `. ./env.sh`"
        base = self.workdir or Path(tempfile.mkdtemp(prefix="pcp-gate-"))
        base.mkdir(parents=True, exist_ok=True)
        # Each check builds in an isolated dir over the shared read-only dependency
        # switch, so parallel workers never race on `.vo` artifacts (PLAN.md 6).
        work = Path(tempfile.mkdtemp(prefix="node-", dir=str(base)))
        try:
            target = work / self.dev.path.name
            target.write_text(assembly.text, encoding="utf-8")
            flags = _rebase_flags(self.flags, self.root, work)
            proc = subprocess.run(
                [coqc, *flags, "-w", "-notation-overridden", target.name],
                cwd=str(work),
                capture_output=True,
                text=True,
                timeout=self.timeout,
            )
            self.last_stdout = proc.stdout or ""
            self.last_stderr = proc.stderr or ""
            return proc.returncode == 0, self.last_stdout + self.last_stderr
        except subprocess.TimeoutExpired:
            self.last_stdout, self.last_stderr = "", ""
            return False, f"coqc timed out after {self.timeout:.0f}s"
        finally:
            if self.workdir is None:
                shutil.rmtree(base, ignore_errors=True)
            else:
                shutil.rmtree(work, ignore_errors=True)


def _binder_names(binders: str) -> list[str]:
    """Names bound by `(x y : T) (z : U)` -- the part before each `:`."""
    names: list[str] = []
    for group in re.findall(r"\(([^()]*)\)|([^\s()]+)", binders):
        text = group[0] or group[1]
        head = text.split(":")[0]
        names.extend(n for n in head.split() if n and n != "_")
    return names




def _statement_present(text: str, target: str, dev: Development, nodes: list[NodeSpec]) -> bool:
    """Item 2: the frozen statement appears verbatim in the assembly.

    True by construction -- patches only ever reach proof-body spans -- but asserted
    anyway, because it is the check the entire freeze rests on and a silent
    regression in span arithmetic would be invisible everywhere else.
    """
    block = dev.block(target)
    statement = block.statement if block else next((n.statement for n in nodes if n.name == target), None)
    return bool(statement) and statement.strip() in text



def _rebase_flags(flags: list[str], root: Path, work: Path) -> list[str]:
    """Make relative ``-Q``/``-R`` paths from ``_CoqProject`` resolve from ``work``."""
    out: list[str] = []
    i = 0
    while i < len(flags):
        if flags[i] in ("-Q", "-R") and i + 2 < len(flags):
            path = flags[i + 1]
            resolved = (root / path).resolve() if not os.path.isabs(path) else Path(path)
            # `.` means "this development": point it at the scratch dir, which holds
            # the assembled file, and keep the original as a second search path.
            if path in (".", "./"):
                out += [flags[i], str(work), flags[i + 2], flags[i], str(resolved), flags[i + 2]]
            else:
                out += [flags[i], str(resolved), flags[i + 2]]
            i += 3
        else:
            out.append(flags[i])
            i += 1
    return out


def _first_error(output: str) -> str:
    lines = output.splitlines()
    for i, line in enumerate(lines):
        if line.startswith("Error") or "Error:" in line:
            return " ".join(l.strip() for l in lines[max(0, i - 1) : i + 3])[:400]
    return _tail(output, 3)[:400]


def _strip_comments(text: str) -> str:
    return re.sub(r"\(\*.*?\*\)", " ", text, flags=re.S)


def parse_assumptions(output: str, names: list[str]) -> dict[str, list[str]]:
    """Parse ``Print Assumptions`` blocks out of coqc's output.

    Rocq prints either ``Closed under the global context`` or ``Axioms:`` followed by
    indented ``name : type`` entries -- and it does *not* echo the command, so the
    blocks are matched to ``names`` positionally, in the order they were appended.
    If the counts do not line up the result is empty rather than misattributed:
    telling the operator that lemma A rests on lemma B's axioms when it does not is
    worse than telling them nothing.
    """
    blocks = [
        b.strip()
        for b in re.split(r"\n(?=Axioms:|Closed under the global context)", output)
        if b.strip().startswith(("Axioms:", "Closed under the global context"))
    ]
    if len(blocks) != len(names):
        return {}
    out: dict[str, list[str]] = {}
    for name, block in zip(names, blocks):
        if block.startswith("Closed under the global context"):
            out[name] = []
        else:
            axioms = [m.group(1) for m in _ASSUMPTION_LINE.finditer(block)]
            out[name] = [a for a in axioms if a not in ("Axioms", "Warning", "Error", "File")]
    return out















