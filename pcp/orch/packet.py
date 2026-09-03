"""The deterministic context packet handed to a prover (PLAN.md 8.6).

A prover receives the frozen statement, its closure, a premise shortlist, the intent
brief, and the nearest solved siblings -- and returns ``qed`` / ``contested`` /
``stuck``.  Everything in the packet is *computed*: no model writes another model's
brief, because that is how idiom drift and quiet statement renegotiation get in.

The packet is also the worker's whole world.  It gets a scratch directory, a `.v`
file it may edit only inside the proof body, and a check command that runs the same
deterministic gate the orchestrator will run -- so "it compiled for me" and "it
passed the gate" are the same sentence.
"""

from __future__ import annotations

import json
import textwrap
from dataclasses import dataclass
from pathlib import Path

from pcp.orch.assemble import Development, NodeSpec
from pcp.orch.graph import Graph, Node

TASK_FILE = "TASK.md"
NODE_FILE = "pcp-node.json"
ANSWER_FILE = "answer.json"
PROOF_FILE = "proof.v"


@dataclass
class PacketPaths:
    workdir: Path
    task: Path
    scratch: Path
    answer: Path
    proof: Path


def build_packet(
    graph: Graph,
    node: Node,
    dev: Development,
    siblings: list[NodeSpec],
    *,
    anchor: str,
    root: Path,
    evidence: str = "",
    attempt: int = 1,
    premises: list[str] | None = None,
    skills: list[str] | None = None,
    state_tools: list[str] | None = None,
    check_command: str = "pcp check",
    docs: list[tuple[str, str]] | None = None,
    tools: list[tuple[str, str]] | None = None,
    library: list[Path] | None = None,
) -> PacketPaths:
    workdir = Path(root) / node.id
    workdir.mkdir(parents=True, exist_ok=True)
    if state_tools:
        # The server is rooted in this node's own workdir, so a worker's proof
        # sessions cannot reach another node's scratch even though they share a
        # binary.  Written per packet rather than once per run for the same reason.
        from pcp.orch.runners.cli import write_mcp_config

        write_mcp_config(workdir, workspace=workdir)
        # ... and say what was granted.  `describe_tools` has warned about exactly
        # this since it was written -- "a granted tool the worker is never told about
        # is an ungranted tool" -- and had no callers, so an ablation that granted
        # ten tools described none of them.  Five of seven workers never touched
        # them; the two that did had spent a turn searching for them first.
        if tools is None:
            tools = describe_tools(list(state_tools))

    # The worker sees the development as it will actually be assembled, with its own
    # node's body left as `admit.` -- so the state it debugs is the state the gate
    # will judge, not an approximation of it.
    assembly = dev.assemble(anchor, siblings, anchor_body=None if node.name != anchor else "admit.", truncate=True)
    scratch = workdir / dev.path.name
    scratch.write_text(assembly.text, encoding="utf-8")
    _copy_project_files(dev.path.parent, workdir)

    # `pcp check` runs inside this directory and needs to know what it is checking.
    (workdir / NODE_FILE).write_text(
        json.dumps(
            {
                "node": node.id,
                "target": node.name,
                "anchor": anchor,
                # Absolute: `pcp check` runs from inside this directory, and a
                # relative path resolved from here points nowhere.
                "file": str(dev.path.resolve()),
                "statement": node.statement,
                "corpus": str(dev.path.parent),
                "siblings": [{"name": s.name, "statement": s.statement, "proved": bool(s.body)} for s in siblings],
                "attempt": attempt,
                # `pcp check` replays a failing proof through petanque to report the
                # goal at the failing tactic.  That replay *is* the state layer, so
                # it is granted with the state tools and withheld without them --
                # otherwise a control arm gets the state layer through the checker
                # and the ablation stops measuring anything.
                "diagnose": bool(state_tools),
            },
            indent=2,
        ),
        encoding="utf-8",
    )

    task = workdir / TASK_FILE
    task.write_text(
        render_task(
            node,
            dev,
            siblings,
            scratch_name=dev.path.name,
            evidence=evidence,
            attempt=attempt,
            premises=premises or [],
            skills=skills or [],
            check_command=check_command,
            docs=docs,
            tools=tools,
            library=list(library or []),
            diagnose=bool(state_tools),
        ),
        encoding="utf-8",
    )
    return PacketPaths(
        workdir=workdir,
        task=task,
        scratch=scratch,
        answer=workdir / ANSWER_FILE,
        proof=workdir / PROOF_FILE,
    )


def _copy_project_files(src: Path, dst: Path) -> None:
    for name in ("_CoqProject", "Makefile", "dune-project"):
        candidate = src / name
        if candidate.exists():
            (dst / name).write_text(candidate.read_text(encoding="utf-8"), encoding="utf-8")


def render_task(
    node: Node,
    dev: Development,
    siblings: list[NodeSpec],
    *,
    scratch_name: str,
    evidence: str = "",
    attempt: int = 1,
    premises: list[str] | None = None,
    skills: list[str] | None = None,
    check_command: str = "pcp check",
    docs: list[tuple[str, str]] | None = None,
    design: str = "",
    tools: list[tuple[str, str]] | None = None,
    library: list[Path] | None = None,
    diagnose: bool = False,
) -> str:
    # `None` means "use whatever documentation is on this machine"; an empty list
    # means "there is none".  Defaulting to None-as-empty silently dropped the
    # documentation section on the eval path.
    docs = default_docs() if docs is None else docs
    parts: list[str] = []
    parts.append(f"# Prove `{node.name}`\n")
    parts.append(
        "You are proving exactly one Rocq/Iris lemma. The statement is **frozen**: it is "
        "owned by the specification side and you may not change it, weaken it, add a "
        "hypothesis to it, or edit any other declaration. Your patch is applied to the "
        "proof body and nothing else -- anything you write outside it is discarded "
        "before it is checked, so editing elsewhere only costs you the attempt.\n"
    )

    parts.append("## The statement\n")
    parts.append(f"```coq\n{node.statement.strip()}\n```\n")

    if node.intent:
        parts.append("## Why this lemma exists\n")
        parts.append(node.intent.strip() + "\n")

    if design:
        # The design brief is context, not a norm, so it goes next to the statement
        # rather than after the answer instructions.
        parts.append(design.strip() + "\n")

    # The node's own statement is not a lemma it may cite, and listing it (with the
    # `admit.` placeholder the assembly needs) would read as "already proved".
    siblings = [s for s in siblings if s.name != node.name]
    if siblings:
        parts.append("## Lemmas you may use\n")
        parts.append(
            "These are in scope in your file. Ones marked *admitted* are type-checked "
            "stubs: cite them freely -- a proof against a stub is exactly the work that "
            "survives once the stub is filled.\n"
        )
        for spec in siblings:
            mark = "proved" if spec.body else "admitted"
            parts.append(f"- `{spec.name}` ({mark}): `{_one_line(spec.statement)}`")
        parts.append("")

    if premises:
        parts.append("## Premise shortlist\n")
        parts.append("Retrieved for this goal; not exhaustive.\n")
        parts.extend(f"- `{p}`" for p in premises)
        parts.append("")

    if evidence:
        # On a resumed node the evidence comes from a previous *run*, so "attempt 0"
        # would be nonsense; say "last time" and leave it at that.
        where = f"attempt {attempt - 1}" if attempt > 1 else "the previous run"
        parts.append(f"## What went wrong last time ({where})\n")
        parts.append("```\n" + evidence.strip()[:4000] + "\n```\n")
        parts.append(
            "Do not repeat the same approach. If the evidence shows a resource was "
            "consumed too early, restructure the destructuring rather than trying the "
            "same tactic again.\n"
        )

    if docs:
        parts.append("## Documentation\n")
        parts.append(
            "You have no way to look this development up, and you do not need one. "
            "The library you are compiling against is on disk, and it is the "
            "authoritative reference -- same version as your goal, unlike anything "
            "online:\n"
        )
        for label, path in docs:
            parts.append(f"- {label}: `{path}`")
        parts.append(
            "\nGrep it rather than guessing a lemma name. A hallucinated name costs a "
            "whole turn; `grep -nE 'Lemma .*↦.*∗' <index>` costs a second.\n"
        )

    if library:
        parts.append(render_library(library))

    if tools:
        parts.append("## Tools available to you\n")
        parts.append(
            "These answer questions about the proof state directly. They are cheaper "
            "and more reliable than re-compiling the file to find out what happened:\n"
        )
        for name, blurb in tools:
            parts.append(f"- `{name}` — {blurb}")
        parts.append(
            "\nPrefer them to hand-rolled shell loops. A previous worker rebuilt "
            "speculative tactic search and proof-state checkpointing out of `cat` and "
            "`coqc`, at one full file compile per candidate; these do the same thing "
            "from a cached proof state.\n"
        )

    parts.append("## How to work\n")
    parts.append(
        textwrap.dedent(
            f"""\
            1. `{scratch_name}` in this directory is the development, assembled the way the
               gate will assemble it. Your lemma's body is `admit.` -- replace it and iterate.
            2. Check your work with `{check_command}`. It runs the same deterministic gate
               the orchestrator runs: compile, `Print Assumptions`, no new admits, no
               global registrations.
            3. When it passes, write your answer and stop.
            """
        )
    )
    if diagnose:
        # The compiler is the one tool every worker reaches for, so this is where a
        # diagnosis is cheapest to deliver: it costs no extra turn and no decision.
        parts.append(
            f"`{check_command}` does more than `coqc` on a failure. When the compile fails "
            "inside a proof body it replays that proof a tactic at a time and reports the "
            "Iris goal **as it stood at the tactic that failed** -- the hypotheses by name, "
            "where your intro pattern and the proposition diverge, what is still in the "
            "spatial context, and which tactics fit the goal's shape. Raw `coqc` cannot tell "
            "you any of that. Prefer it to a bare compile.\n"
        )

    parts.append("## How to answer\n")
    parts.append(
        f"Write `{ANSWER_FILE}` in this directory. Exactly one of three shapes -- there "
        "is no fourth, and a partial edit is not an answer:\n"
    )
    parts.append(
        "```json\n"
        + json.dumps({"status": "qed", "proof": "iIntros \"[H1 H2]\".\niFrame."}, indent=2)
        + "\n```\n"
    )
    parts.append(
        "```json\n"
        + json.dumps(
            {
                "status": "stuck",
                "evidence": "where you got stuck and what the goal was",
                "requests": [
                    {"statement": "Lemma helper ... .", "rationale": "why this would unblock it"}
                ],
            },
            indent=2,
        )
        + "\n```\n"
    )
    parts.append(
        "```json\n"
        + json.dumps(
            {"status": "contested", "evidence": "why you believe the statement itself is wrong"},
            indent=2,
        )
        + "\n```\n"
    )
    parts.append(
        "`requests` are lemmas you would like to exist. You cannot create them yourself: "
        "they go back to whoever stated this node, get checked, and are frozen before "
        "anyone proves them. A request that just restates your own goal is rejected "
        "automatically, so do not file one.\n"
    )
    parts.append(
        "**Never add a hypothesis to make the proof go through.** If you think the "
        "statement needs one, that is `contested` with a reason -- not a proof.\n"
    )

    for skill in skills or []:
        parts.append(f"\n---\n\n{skill.strip()}\n")

    return "\n".join(parts)


def describe_tools(names: list[str]) -> list[tuple[str, str]]:
    """Blurbs for the granted MCP tools, in the worker's terms.

    A granted tool the worker is never told about is an ungranted tool: the first
    run with the ledger rung wired used none of them, because nothing in the packet
    said they existed.
    """
    from pcp.orch.runners.cli import mcp_tool_name

    blurbs = {
        "proof_open": "open this lemma and get its Iris proof state, per hypothesis",
        "proof_step": "run one tactic from the current state and see exactly what changed "
                      "— no file edit, no recompile",
        "proof_state": "render the current goal under a token budget; says what it elided",
        "proof_ledger": "where did a hypothesis go? what consumed it? what is still live?",
        "proof_try": "run up to 20 candidate tactics from one state and report which survive",
        "proof_destruct": "compile an iDestruct/iIntros pattern from the hypothesis' structure, "
                          "or find out exactly where your pattern and the prop diverge",
        "premise_search": "search for a lemma *at this goal*, instead of guessing a name",
        "notation_resolve": "what a notation means, what it unfolds to, which tactics apply",
        "proof_trace": "replay a script and get the resource-ledger event log",
        "verify_node": "run the deterministic gate on a proof body",
    }
    return [(mcp_tool_name(n), blurbs.get(n, "")) for n in names if n in blurbs]


def render_library(paths: list[Path]) -> str:
    """Say what a run was given beyond its own development.

    Granting a directory and not naming it repeats the `describe_tools` mistake --
    an ablation once granted ten tools and described none, and five of seven workers
    never found them.  Whatever a rung is allowed, the packet says so out loud, both
    so the worker uses it and so the trace records what it had.
    """
    lines = ["## What you may consult\n"]
    lines.append(
        "You have been given, read-only, what this system itself produced on the "
        "problems below this one, plus any reading listed here. Treat a previous "
        "solution as a worked example of *this* codebase's idiom -- the ghost state "
        "it settled on, the shape of its invariants, how its atomic updates are "
        "opened -- not as something to copy. The problem here is different.\n"
    )
    for path in paths:
        directory = Path(path)
        note = _library_note(directory)
        lines.append(f"- `{directory}`" + (f" — {note}" if note else ""))
        # List the files, do not just name the directory.  The decomposer is granted
        # Read/Glob/Grep and no Bash on purpose, and one run spent a turn on a
        # blocked `ls -la` of exactly this directory.  Naming a resource is not the
        # same as making it reachable with the tools the reader actually has.
        for entry in _library_files(directory):
            lines.append(f"    - `{entry}`")
    lines.append("")
    return "\n".join(lines)


#: Enough to name a solution plus its project files and a paper in two formats.
_LIBRARY_LISTING = 12


def _library_files(directory: Path) -> list[Path]:
    try:
        entries = sorted(p for p in directory.rglob("*") if p.is_file())
    except OSError:
        return []
    return [p for p in entries if p.name not in ("README.md", "LIBRARY.md")][:_LIBRARY_LISTING]


def _library_note(path: Path) -> str:
    """The first non-empty line of a directory's own README, if it wrote one."""
    for name in ("README.md", "LIBRARY.md"):
        readme = path / name
        if readme.exists():
            for line in readme.read_text(encoding="utf-8", errors="replace").splitlines():
                stripped = line.strip().lstrip("#").strip()
                if stripped:
                    return stripped[:200]
    return ""


def default_docs() -> list[tuple[str, str]]:
    """Local documentation a worker can reach with no network at all."""
    import os

    out: list[tuple[str, str]] = []
    index = Path(".pcp/docs/index.txt").resolve()
    if index.exists():
        out.append(("every declaration in Iris and std++, one per line", str(index)))
    for var in ("ROCQPATH", "COQPATH"):
        for entry in (os.environ.get(var) or "").split(":"):
            if entry and (Path(entry) / "iris").exists():
                out.append(("the Iris and std++ sources themselves", entry))
                return out
    return out


def _one_line(text: str, width: int = 110) -> str:
    one = " ".join(text.split())
    return one if len(one) <= width else one[: width - 1] + "…"
