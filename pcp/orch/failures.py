"""Failure classification, so a benchmark run says *what to fix* (PLAN.md 1, 13).

A solve rate is a number; a failure taxonomy is a work queue.  Classification is
deterministic and honest about its limits: anything it cannot place lands in
``unclassified`` rather than being forced into the nearest bucket.

What changed from the legacy classifier, and why (each is a bug in
``SCRATCH/bugs-orch-core.md``):

* the runner's exit status, ``NodeResult.status == "error"`` and a gate that could
  not run are **first-class inputs**, not regex targets -- so a compile error on
  line 401 is a compile error and a sandbox that failed to start is not a stuck
  worker (``runner-error``);
* every regex is anchored or word-bounded: ``Resolve`` no longer matches
  ``unresolved``, ``AU`` no longer matches ``au``;
* ``gate-violation`` fires only on a ``[FAIL]`` line of a gate report, never on the
  check *names*, which every report prints;
* the gate's own compile timeout is infrastructure, never the worker's ``deadline``;
* :func:`summarize` classifies every record with exactly the inputs
  :func:`classify_record` uses when the record is written, so ``pcp failures`` and
  ``record.json`` agree.

Stdlib only: the streaming runner imports this at capture time.
"""

from __future__ import annotations

import re
from collections import Counter
from collections.abc import Iterable
from dataclasses import dataclass, field
from typing import Any

#: Detail prefix the gate uses when it could not run at all (missing/timed-out coqc).
GATE_COULD_NOT_RUN = "gate could not run:"

#: The taxonomy (contract §1.12).  The first seven are PLAN.md 1's list, in its order;
#: the rest are failures of the *pipeline* rather than of Iris reasoning.
TAXONOMY: dict[str, str] = {
    "premature-consumption": "a spatial hypothesis was eliminated early and needed later",
    "leftover-spatial": "iFrame/done failed because the spatial context was not empty",
    "mask-arithmetic": "invariant masks did not line up (↑N ⊆ E, E ∖ ↑N, open/close pairing)",
    "later-modality": "missing iNext / iMod at the wrong point / ▷ depth mismatch",
    "persistent-vs-spatial": "treated a persistent hypothesis as consumed, or vice versa",
    "retrieval": "referred to a lemma or instance that does not exist",
    "context-pollution": "ran out of context, or drowned in goal dumps",
    "pattern-mismatch": "an iDestruct/iIntros pattern did not fit its object",
    "evaluation-position": "wp_bind/wp_pure could not find the expected redex in the program term",
    "incomplete-proof": "the script ran out of tactics with goals still open",
    "permission-denied": "the harness's own permission layer blocked a command",
    "unification-failure": "iApply/wp_apply could not match a lemma's conclusion to the goal",
    "prophecy-atomicity": "logically atomic bookkeeping: atomic update, commit point, prophecy resolution",
    "no-progress": "the worker looped or made no state progress before its deadline",
    "deadline": "the worker ran out of wall clock",
    "gate-violation": "the patch was rejected by the deterministic gate (admit, global, escape hatch)",
    "protocol-violation": "the worker produced no usable answer in the required shape",
    "contested": "the worker argued the statement itself is wrong",
    "scope-or-type-error": "a term elaborated at the wrong type -- usually a missing %Z/%nat scope",
    "state-tool-error": "a pcp proof-state tool failed to run (often: the file does not compile)",
    "focus-or-bullet": "bullets/braces did not match the goals actually open",
    "specialization": "iSpecialize could not instantiate a wand, or its hypothesis was gone",
    "runner-error": "the provider or its CLI failed; not a proof failure",
    "unclassified": "no rule matched -- read the record",
}
assert len(TAXONOMY) == 24

_I = re.IGNORECASE
_M = re.MULTILINE
#: (class, regex, weight).  Weight breaks ties when several rules fire; higher wins.
_RULES: list[tuple[str, re.Pattern[str], int]] = [
    ("leftover-spatial", re.compile(r"spatial context is not empty|\biFrame\b.*\bcannot\b|not all resources|cannot solve.*\bemp\b", _I), 6),
    ("pattern-mismatch", re.compile(r"\biOrDestruct\b|\biAndDestruct\b|cannot destruct|pattern/prop mismatch|not a disjunction|intro pattern", _I), 7),
    ("mask-arithmetic", re.compile(r"\bmasks?\b|↑\w+ ⊆|∖ ↑|\bfupd_mask\b|invariant .* already open|\bnot\b.*\bdisjoint\b", _I), 6),
    ("later-modality", re.compile(
        r"\biNext\b|▷|\blater\b|\btimeless\b|\bMaybeIntoLaterN\b|is not later|"
        r"\biModIntro\b[^\n]*not a modality|goal is not a modality|\bIntoModal\b", _I), 5),
    ("persistent-vs-spatial", re.compile(r"not persistent|\bIntoPersistent\b|Persistent .* instance|intuitionistic context", _I), 6),
    ("evaluation-position", re.compile(r"\bwp_(?:bind|pure|apply)\b[^\n]*cannot find|is not a redex|not a value|no (?:such )?evaluation context", _I), 9),
    ("retrieval", re.compile(r"was not found in the current environment|Unknown (?:constant|reference)|The reference \S+ was not found|Cannot find an? (?:instance|lemma)", _I), 8),
    ("incomplete-proof", re.compile(r"Attempt to save an incomplete proof|There are still unproven goals|remaining open goals", _I), 9),
    ("permission-denied", re.compile(
        r"requires approval|permission to use|was not granted|blocked by the permission|"
        r"was blocked\. For security|command contains multiple operations", _I), 20),
    ("unification-failure", re.compile(r"Unable to unify|cannot unify|\bnot\b.*\bconvertible\b|\biApply\b.*\bfailed\b|no matching clauses|Impossible to unify", _I), 6),
    # Case-sensitive on purpose: `Resolve` matched "unresolved" and `AU ` matched "au".
    ("prophecy-atomicity", re.compile(r"\batomic_update\b|\bAU\b|\bwp_resolve\b|\bNewProph\b|\bResolve\b|commit point|\batomic\b.*\babort\b"), 3),
    ("premature-consumption", re.compile(r"was consumed at step|repair class: (?:split-differently|frame-later)|no such (?:hypothesis|ident)|not found in the context", _I), 7),
    ("scope-or-type-error", re.compile(
        r'The term "[^"]*" has type "[^"]*" while it is expected to have type|'
        r"has type .{0,40} while it is expected to have type|"
        r"Illegal application|Non-functional construction|"
        r'is expected to have type "?nat|cannot be applied to', _I), 8),
    ("specialization", re.compile(r"\biSpecialize\b[^\n]*(?:cannot instantiate|not found|could not)", _I), 7),
    ("state-tool-error", re.compile(
        r"Error executing tool (?:mcp__pcp__)?\w+|\bpet-server\b|\bpetanque\b|"
        r"no petanque binary|state \d+ is no longer in the LRU", _I), 12),
    ("focus-or-bullet", re.compile(
        r"proof is focused, but cannot be unfocused|Wrong bullet|No such (?:bullet|goal)|"
        r"[Tt]his subproof is complete|not the last goal", _I), 8),
    # Only a failing line of the gate report -- the names appear in every report.
    ("gate-violation", re.compile(
        r"^\s*\[FAIL\] (?:no new Admitted|no escape hatches|ambient-state hygiene|axiom hygiene|"
        r"statement pinning|`Proof using` discipline|body is a single proof|design contract)", _M), 9),
    ("protocol-violation", re.compile(
        r"produced no answer\.json|malformed answer\.json|no fenced proof block|no scripted answer|"
        r"wrote no answer\.json|qed with no proof body", _I), 9),
    ("protocol-violation", re.compile(
        r"must be an object|must be a list|is not a Rocq identifier|is not an identifier|"
        r"has no statement|has no text|produced no JSON object|is not a Require line", _I), 19),
    # The runner's own wording only; a Rocq `Timeout` and the gate's coqc timeout are not
    # the worker's deadline.
    ("deadline", re.compile(r"exceeded its \S+ deadline|killed at (?:its|the) deadline|worker (?:timed out|was killed)", _I), 8),
    ("no-progress", re.compile(r"showed no progress|loop detected|state hash repeat", _I), 8),
    ("runner-error", re.compile(
        r"is not on PATH|\bunauthenticated\b|API call failed|provider error|rate limit|"
        r"Failed to authenticate|access token has been revoked|\bHTTP 401\b|\bstatus 401\b|"
        r"\b401 Unauthorized\b|invalid[_ ]api[_ ]key|^bwrap:|Can't find source path|\bexecvp\b|"
        r"No such file or directory: '/tmp/pcp-|command not found|Input must be provided|"
        + re.escape(GATE_COULD_NOT_RUN) + r"|no coqc on PATH", _I | _M), 20),
    ("context-pollution", re.compile(r"context (?:window|length) exceeded|too many tokens|prompt is too long", _I), 10),
]

#: Classes a *transcript* may establish on its own against evidence that already says
#: something: the harness failing underneath the worker.  Iris vocabulary in a
#: transcript says what the worker wrote about, not what failed.
_FROM_CONTEXT = frozenset({"runner-error", "permission-denied", "context-pollution", "deadline", "no-progress"})

_SYNTAX = re.compile(r"Syntax error|expected after|Illegal begin of|Unexpected token", _I)
#: Tool results that are file contents, not error reports (a markdown heading is fine).
_NOT_AN_ERROR = re.compile(
    r'^\s*(?:"""|/\*)|^\s*\d+[:\t]|\bin line:|PLAN\.md|def \w+\(|^\s*import \w+|^\s*Exit code \d+\s*$', _M
)
_PACKET_FILES = ("_CoqProject", "pcp-node.json", "TASK.md", "answer.json", "proof.v", ".mcp.json")
_COMPLAINT = (
    r"(?:The term\b|Unable to unify\b|Cannot \w|Illegal\b|The reference\b|Found no\b"
    r"|Impossible to unify\b|In the projection\b|No such\b|The command has indeed failed\b)"
)
_ENVIRONMENT_DUMP = re.compile(r"In environment\b.*?(?=" + _COMPLAINT + ")", re.S)
_DIAGNOSIS_FIELD = re.compile(r'["\']?diagnosis["\']?\s*:\s*"(?:[^"\\]|\\.)*"', re.S)
_NO_ANSWER = re.compile(r"produced no answer\.json|wrote no answer\.json|produced no output|no answer", _I)


# ------------------------------------------------------------------ preprocessing

def strip_our_own_diagnosis(text: str) -> str:
    """Drop the diagnosis ``pcp check`` attached: the taxonomy reads the compiler, never us."""
    return _DIAGNOSIS_FIELD.sub("", text or "")


def collapse_environment(text: str) -> str:
    """Drop Rocq's ``In environment`` binder dump, keeping the complaint after it."""
    return _ENVIRONMENT_DUMP.sub("In environment [...] ", text or "")


_ESCAPE = re.compile(r'\\u([0-9a-fA-F]{4})|\\(["\\/nrt])')
_SIMPLE = {'"': '"', "\\": "\\", "/": "/", "n": "\n", "r": "\r", "t": "\t"}
_JSON_MARKER = re.compile(r'\\u[0-9a-fA-F]{4}|\\["nt]')


def unescape(text: str) -> str:
    """Decode a JSON-escaped fragment (up to three layers) so Iris notation is readable.

    Only text that carries a real JSON escape (``\\uXXXX``, ``\\"``, ``\\n``) is
    touched: Rocq's own ``\\/`` in plain evidence must stay ``\\/``.
    """
    for _ in range(3):
        if not _JSON_MARKER.search(text):
            return text
        nxt = _ESCAPE.sub(lambda m: chr(int(m.group(1), 16)) if m.group(1) else _SIMPLE[m.group(2)], text)
        if nxt == text:
            return text
        text = nxt
    return text


def preprocess(text: str) -> str:
    """The one preprocessing chain, used at write time and at report time alike."""
    return collapse_environment(strip_our_own_diagnosis(unescape(text or "")))


def looks_like_an_error(text: str) -> bool:
    """Cheap guard against classifying file contents the worker happened to read."""
    if not text or len(text.strip()) < 5:
        return False
    if _NOT_AN_ERROR.search(text[:200]) and not re.search(r"^\s*Error:", text, _M):
        return False
    return not _is_a_directory_listing(text)


def _is_a_directory_listing(text: str) -> bool:
    words = [w for w in re.split(r"[\s,]+", text.strip()) if w]
    if not words or len(words) > 16:
        return False
    hits = sum(1 for w in words if w in _PACKET_FILES or w.endswith(".v") or w.startswith("Exit"))
    return hits >= 2 and hits >= len(words) - 2


# ------------------------------------------------------------------ classification

@dataclass(frozen=True)
class Finding:
    klass: str
    evidence: str = ""

    @property
    def description(self) -> str:
        return TAXONOMY.get(self.klass, "")

    def to_json(self) -> dict[str, str]:
        return {"klass": self.klass, "evidence": self.evidence}


@dataclass
class Classification:
    findings: list[Finding] = field(default_factory=list)

    @property
    def primary(self) -> str:
        return self.findings[0].klass if self.findings else "unclassified"

    @property
    def classes(self) -> list[str]:
        return [f.klass for f in self.findings]

    @property
    def evidence(self) -> str:
        return self.findings[0].evidence if self.findings else ""

    def render(self) -> str:
        return ", ".join(self.classes) if self.findings else "unclassified"

    def to_json(self) -> dict[str, Any]:
        return {"primary": self.primary, "classes": self.classes, "evidence": self.evidence}


def classify(
    evidence: str | None,
    *,
    context: str = "",
    exit_code: int | None = None,
    is_error: bool = False,
    infrastructure: bool = False,
    status: str | None = None,
) -> Classification:
    """Classify one failed attempt.

    ``evidence`` is what the attempt reported (worker evidence, gate report, compiler
    output -- already joined); ``context`` is the transcript, which may only establish
    harness failures unless nothing else fired.  ``exit_code`` (the runner process),
    ``is_error`` (``NodeResult.status == "error"``) and ``infrastructure`` (the gate
    could not run) are structured inputs that outrank every regex.
    """
    if status == "contested":
        return Classification([Finding("contested", "the worker argued the statement itself is wrong")])
    if status == "error":
        is_error = True
    text = preprocess(evidence or "")
    infra: Finding | None = None
    if infrastructure:
        infra = Finding("runner-error", "the gate could not run (infrastructure); the worker is not to blame")
    elif is_error:
        infra = Finding("runner-error", "the runner reported an infrastructure error: " + _tail(text, 120))
    elif exit_code not in (None, 0) and (not text.strip() or _NO_ANSWER.search(text)):
        infra = Finding("runner-error", f"the runner exited with status {exit_code} and no answer was produced")
    found = _classify_text(text)
    if context:
        widened = _classify_text(text + "\n" + preprocess(context) if text.strip() else preprocess(context))
        if found.primary == "unclassified" or widened.primary in _FROM_CONTEXT:
            found = widened
    if infra is None:
        return found
    rest = [f for f in found.findings if f.klass not in ("runner-error", "unclassified")]
    if is_error and not infrastructure and exit_code in (None, 0) and found.primary == "protocol-violation":
        # A malformed answer recorded with status ``error`` (the decomposer files its
        # proposal violations that way) is a shape problem first, an outage second.
        return Classification([rest[0], infra, *rest[1:]])
    return Classification([infra, *rest])


def _classify_text(text: str) -> Classification:
    if not text.strip():
        return Classification([Finding("unclassified", "no evidence was recorded")])
    if not looks_like_an_error(text):
        return Classification([Finding("unclassified", "not an error report: " + _tail(text, 80))])
    hits: list[tuple[int, Finding]] = []
    for klass, pattern, weight in _RULES:
        m = pattern.search(text)
        if m:
            hits.append((weight, Finding(klass, _window(text, m))))
    if not hits:
        if _SYNTAX.search(text):
            return Classification([Finding("protocol-violation", "Rocq syntax error in the worker's script")])
        return Classification([Finding("unclassified", _tail(text))])
    hits.sort(key=lambda h: -h[0])
    seen: set[str] = set()
    findings = []
    for _w, f in hits:
        if f.klass not in seen:
            seen.add(f.klass)
            findings.append(f)
    return Classification(findings)


def _window(text: str, m: re.Match[str], width: int = 90) -> str:
    start = max(0, m.start() - width // 2)
    return " ".join(text[start : m.end() + width // 2].split())


def _tail(text: str, n: int = 200) -> str:
    return " ".join(text.strip().split())[-n:]


# ------------------------------------------------------------------ records

def gate_infrastructure(checks: Iterable[dict[str, Any]]) -> bool:
    """Whether a stored ``gate_checks`` list says the gate could not run."""
    for c in checks or []:
        if str(c.get("name", "")).startswith("compiles") and str(c.get("detail", "")).startswith(GATE_COULD_NOT_RUN):
            return True
    return False


def record_evidence(rec: dict[str, Any]) -> str:
    """The evidence text a record is classified on: worker evidence, gate report, compiler tail."""
    parts = [rec.get("evidence") or "", rec.get("gate_report") or "", rec.get("compile_output") or ""]
    return "\n".join(p for p in parts if p)


def classify_record(rec: dict[str, Any]) -> Classification:
    """Classify a record dict with the same inputs at write time and at report time."""
    return classify(
        record_evidence(rec),
        context=rec.get("transcript_tail") or "",
        exit_code=rec.get("exit_code"),
        status=rec.get("status") or "stuck",
        infrastructure=gate_infrastructure(rec.get("gate_checks") or []),
    )


def friction_classes(rec: dict[str, Any]) -> list[tuple[str, str]]:
    """``(class, text)`` for every error the worker hit *and recovered from*."""
    out: list[tuple[str, str]] = []
    for err in (rec.get("trace") or {}).get("errors", []) or []:
        text = preprocess(str(err))
        if not looks_like_an_error(text):
            continue
        out.append((classify(text).primary, text))
    return out


@dataclass
class FailureReport:
    total: int = 0
    solved: int = 0
    primary: Counter = field(default_factory=Counter)
    all_classes: Counter = field(default_factory=Counter)
    examples: dict[str, list[str]] = field(default_factory=dict)
    friction: Counter = field(default_factory=Counter)
    friction_examples: dict[str, list[str]] = field(default_factory=dict)
    turns: list[int] = field(default_factory=list)
    checks: list[int] = field(default_factory=list)

    def render(self, limit: int = 3) -> str:
        failed = self.total - self.solved
        lines = [f"{self.solved}/{self.total} solved · {failed} failed"]
        if self.turns or self.checks:
            lines.append(f"  effort: {_mean(self.turns):.1f} turns, {_mean(self.checks):.1f} gate checks per attempt")
        if self.primary:
            lines.append("")
            lines.append("failures, by primary class:")
            width = max(len(k) for k in self.primary)
            for klass, n in self.primary.most_common():
                share = 100 * n / max(1, failed)
                lines.append(f"  {klass:<{width}}  {n:>3}  {share:4.0f}%   {TAXONOMY.get(klass, '')}")
                for ex in self.examples.get(klass, [])[:limit]:
                    lines.append(f"      · {ex[:140]}")
            secondary = [k for k, _ in self.all_classes.most_common() if k not in self.primary]
            if secondary:
                lines.append("  also present (not primary): " + ", ".join(secondary))
        if self.friction:
            lines.append("")
            lines.append("friction -- errors workers recovered from (including on solves):")
            width = max(len(k) for k in self.friction)
            for klass, n in self.friction.most_common():
                lines.append(f"  {klass:<{width}}  {n:>3}   {TAXONOMY.get(klass, '')}")
                for ex in self.friction_examples.get(klass, [])[:limit]:
                    lines.append(f"      · {ex[:140]}")
        if not self.primary and not self.friction:
            lines.append("  (nothing to report -- no failures and no recorded friction)")
        return "\n".join(lines)

    def to_json(self) -> dict[str, Any]:
        return {
            "total": self.total,
            "solved": self.solved,
            "primary": dict(self.primary),
            "all_classes": dict(self.all_classes),
        }


def _mean(values: list[int]) -> float:
    return sum(values) / len(values) if values else 0.0


def summarize(records: Iterable[dict[str, Any]]) -> FailureReport:
    """Aggregate per-attempt records into a work queue (same classifier as the writer)."""
    report = FailureReport()
    for rec in records:
        report.total += 1
        trace = rec.get("trace") or {}
        if trace.get("turns"):
            report.turns.append(int(trace["turns"]))
        if trace.get("check_iterations") is not None:
            report.checks.append(int(trace["check_iterations"]))
        for klass, text in friction_classes(rec):
            report.friction[klass] += 1
            report.friction_examples.setdefault(klass, []).append(
                f"{rec.get('lemma', '?')}: {' '.join(text.split())[:120]}"
            )
        if rec.get("solved"):
            report.solved += 1
            continue
        c = classify_record(rec)
        report.primary[c.primary] += 1
        for klass in c.classes:
            report.all_classes[klass] += 1
        report.examples.setdefault(c.primary, []).append(f"{rec.get('lemma', '?')}: {c.evidence}")
    return report
