"""The deterministic context packet handed to a prover (PLAN.md 8.6; contract §3.1).

A prover receives the frozen statement, the intent brief, its siblings as stubs, a
scratch ``.v`` assembled exactly as the gate will assemble it, and a check command
that runs the same gate -- so "it compiled for me" and "it passed the gate" are the
same sentence.  Everything in the packet is *computed*: no model writes another
model's brief.

Every attempt gets a **fresh** directory ``<root>/<node.id>/a<attempt_id>/`` (removed
first if it exists), so a stale ``answer.json`` from attempt 1 can never be read as
attempt 2's answer (ARCHITECTURE.md §8).

A retry that follows a killed or failed attempt gets the recovered partial proof in
the scratch file *and* under its own heading (PLAN.md 6: "requeue with the partial
trace as evidence"), rather than starting from ``admit.`` and being told a partial
existed.
"""

from __future__ import annotations

import json
from collections.abc import Iterable
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from pcp.config.env import iris_root
from pcp.mcp.config import write_mcp_config
from pcp.mcp.names import describe_tools
from pcp.orch.model import Node
from pcp.orch.protocol import (
    ADJUDICATED_MARKER,
    AMENDED_MARKER,
    ANSWER_FILE,
    NODE_FILE,
    PROOF_FILE,
    TASK_FILE,
)
from pcp.rocq.assemble import Development, NodeSpec
from pcp.util.io import atomic_write_text, copy_if_exists, ensure_dir, json_dump, read_text, rm_tree
from pcp.util.text import one_line

PLACEHOLDER_BODY = "admit."
PROJECT_FILES = ("_CoqProject", "Makefile", "dune-project")
#: Enough to name a solution plus its project files and a paper in two formats.
LIBRARY_LISTING = 12
EVIDENCE_LIMIT = 4000
#: An evidence string starting with one of these is not a failure report but a
#: message from the orchestrator about *why* the node is open again; the packet
#: titles the section accordingly and drops the "do not repeat yourself" advice.
EVIDENCE_HEADINGS: dict[str, tuple[str, str]] = {
    AMENDED_MARKER: (
        "The design changed since your last attempt",
        "A definition you (or a sibling) depend on now carries more than it did. Read "
        "what changed before you read your old failure: the goal at the site where you "
        "got stuck is different now, and the fact you were missing may simply be there "
        "when you open the invariant. Your partial proof, if any, is in the scratch file.\n",
    ),
    ADJUDICATED_MARKER: (
        "Your contest was reviewed: the statement stands",
        "An approver read your argument against this statement and disagrees; the hint "
        "above says where the strategy should differ. Do not contest it again on the "
        "same grounds -- change the approach.\n",
    ),
}


#: The adjudication detail's tail when the node was *reviewed* after failed attempts
#: rather than contested (``AmendmentRun.adjudicate`` writes it); the heading differs
#: because the prover never claimed the statement was wrong.
REVIEWED_TAIL = "Your last attempt's evidence was:"
REVIEWED_HEADING = (
    "Your attempts were reviewed: the statement stands",
    "An approver read your failed attempts and finds this statement provable as written; "
    "the hint above says what to do differently. Contest it only if you find the statement "
    "itself wrong.\n",
)


@dataclass(frozen=True)
class PacketPaths:
    workdir: Path
    task: Path
    scratch: Path
    answer: Path
    proof: Path
    node_file: Path


def attempt_dir(root: str | Path, node_id: str, attempt_id: int) -> Path:
    return Path(root) / node_id / f"a{attempt_id}"


def build_packet(
    graph: Any,
    node: Node,
    dev: Development,
    siblings: list[NodeSpec],
    *,
    anchor: str,
    root: str | Path,
    attempt_id: int,
    evidence: str = "",
    attempt: int = 1,
    premises: list[str] | None = None,
    skills: list[str] | None = None,
    state_tools: list[str] | None = None,
    check_command: str = "pcp check",
    docs: list[tuple[str, str]] | None = None,
    tools: list[tuple[str, str]] | None = None,
    library: list[Path] | None = None,
    design: str = "",
    previous_body: str = "",
    index_path: str | Path | None = None,
    extra_preamble: str = "",
) -> PacketPaths:
    """Write the worker's whole world into a fresh attempt directory.

    ``siblings`` may include the node itself; its body is replaced by the placeholder
    (or ``previous_body``) and it is never listed as proved.  ``graph`` is accepted
    for API symmetry with the scheduler and not consulted: the packet is a function
    of its arguments, which is what makes it deterministic.  ``extra_preamble`` is
    the plan's own preamble (extra ``Require`` lines): it goes into the scratch file
    exactly as the gate inserts it, and into ``pcp-node.json`` so ``pcp check`` can
    do the same (PLAN.md 8.11).
    """
    del graph
    workdir = attempt_dir(root, node.id, attempt_id)
    rm_tree(workdir)
    ensure_dir(workdir)

    body = previous_body.strip() or PLACEHOLDER_BODY
    others = [s for s in siblings if s.name != node.name]
    if node.name == anchor:
        specs, anchor_body = others, body
    else:
        own = next((s for s in siblings if s.name == node.name), None)
        own_spec = NodeSpec(node.name, own.statement if own else node.statement, body, own.mockable if own else True, node.transparent or bool(own and own.transparent))
        specs = [own_spec if s.name == node.name else s for s in siblings] if own else [*others, own_spec]
        anchor_body = None
    assembly = dev.assemble(anchor, specs, anchor_body=anchor_body, truncate=True, extra_preamble=extra_preamble)
    scratch = workdir / dev.path.name
    atomic_write_text(scratch, assembly.text)
    for name in PROJECT_FILES:
        copy_if_exists(dev.path.parent / name, workdir / name)

    if state_tools:
        # Rooted per node so a worker's proof sessions cannot reach another node's
        # scratch; and every granted tool is described, because a granted tool the
        # worker is never told about is an ungranted tool.
        write_mcp_config(workdir, workspace=workdir)
        if tools is None:
            tools = describe_tools(list(state_tools))

    node_file = workdir / NODE_FILE
    json_dump(
        node_file,
        {
            "node": node.id,
            "target": node.name,
            "anchor": anchor,
            "file": str(dev.path.resolve()),
            "statement": node.statement,
            "corpus": str(dev.path.resolve().parent),
            "siblings": [
                {"name": s.name, "statement": s.statement, "proved": s.body is not None and s.name != node.name}
                for s in siblings
            ],
            "attempt": attempt,
            "diagnose": bool(state_tools),
            "attempt_id": attempt_id,
            "scratch": dev.path.name,
            "preamble": extra_preamble,
        },
    )
    task = workdir / TASK_FILE
    atomic_write_text(
        task,
        render_task(
            node, dev, siblings,
            scratch_name=dev.path.name, evidence=evidence, attempt=attempt, premises=premises or [],
            skills=skills or [], check_command=check_command, docs=docs, design=design, tools=tools,
            library=list(library or []), diagnose=bool(state_tools), previous_body=previous_body,
            index_path=index_path,
        ),
    )
    return PacketPaths(
        workdir=workdir, task=task, scratch=scratch, answer=workdir / ANSWER_FILE,
        proof=workdir / PROOF_FILE, node_file=node_file,
    )


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
    previous_body: str = "",
    index_path: str | Path | None = None,
) -> str:
    """``TASK.md``, sections in the contract's order (§3.1).  Same inputs, same bytes."""
    del dev
    # None means "whatever is on this machine"; [] means "none" -- collapsing the two
    # once silently dropped the documentation section on the eval path.
    docs = default_docs(index_path) if docs is None else docs
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
        parts.append(design.strip() + "\n")

    others = [s for s in siblings if s.name != node.name]
    if others:
        parts.append("## Lemmas you may use\n")
        parts.append(
            "These are in scope in your file. Ones marked *admitted* are type-checked "
            "stubs: cite them freely -- a proof against a stub is exactly the work that "
            "survives once the stub is filled.\n"
        )
        for spec in others:
            mark = "proved" if spec.body is not None else "admitted"
            parts.append(f"- `{spec.name}` ({mark}): `{one_line(spec.statement)}`")
        parts.append("")
    if premises:
        parts.append("## Premise shortlist\n")
        parts.append("Retrieved for this goal; not exhaustive.\n")
        parts.extend(f"- `{p}`" for p in premises)
        parts.append("")
    if evidence:
        parts.extend(render_evidence(evidence, attempt=attempt))
    if previous_body.strip():
        parts.append("## Your previous attempt's proof (partial)\n")
        parts.append(
            f"The proof body below was recovered from the previous attempt and is already in "
            f"`{scratch_name}` in place of `{PLACEHOLDER_BODY}`. It did not pass the gate: continue "
            "from it or replace it, but do not start from nothing without reading it.\n"
        )
        parts.append(f"```coq\n{previous_body.strip()}\n```\n")
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
        f"1. `{scratch_name}` in this directory is the development, assembled the way the\n"
        f"   gate will assemble it. Your lemma's body is `{PLACEHOLDER_BODY}` -- replace it and iterate.\n"
        f"2. Check your work with `{check_command}`. It runs the same deterministic gate\n"
        "   the orchestrator runs: compile, `Print Assumptions`, no new admits, no\n"
        "   global registrations. Run it in the FOREGROUND and wait for it: this session\n"
        "   is headless, so a background task, a scheduled wake-up, or ending your turn\n"
        "   to wait for something ends the session and loses the attempt.\n"
        "3. When it passes, write your answer and stop.\n"
    )
    if diagnose:
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
    parts.append("```json\n" + json.dumps({"status": "qed", "proof": 'iIntros "[H1 H2]".\niFrame.'}, indent=2) + "\n```\n")
    parts.append(
        "```json\n"
        + json.dumps(
            {
                "status": "stuck",
                "evidence": "where you got stuck and what the goal was",
                "requests": [{"statement": "Lemma helper ... .", "rationale": "why this would unblock it"}],
                "amendments": [
                    {"definition": "my_inv", "add": "▷ Q", "at": "closing the invariant after the CmpXchg", "why": "..."}
                ],
            },
            indent=2,
            ensure_ascii=False,
        )
        + "\n```\n"
    )
    parts.append(
        "```json\n"
        + json.dumps({"status": "contested", "evidence": "why you believe the statement itself is wrong"}, indent=2)
        + "\n```\n"
    )
    parts.append(
        "`requests` are lemmas you would like to exist. You cannot create them yourself: "
        "they go back to whoever stated this node, get checked, and are frozen before "
        "anyone proves them. A request that just restates your own goal is rejected "
        "automatically, so do not file one.\n"
    )
    parts.append(
        "If the proof needs a fact the invariant does not carry, ask for it in "
        "`amendments` (the definition, the fact, the goal where you needed it). A "
        "strengthening that compiles is applied mechanically and every affected proof "
        "is replayed; you do not need to contest the statement for this. Keep proving "
        "the branches that do not need it first -- a partial proof is kept and comes "
        "back to you with the change. `add` is a conjunct joined onto the definition's "
        "body; `replace` (the complete new `Definition ... .` sentence) is for anything "
        "else and is reviewed before it is applied.\n"
    )
    parts.append(
        "**Never add a hypothesis to make the proof go through.** If you think the "
        "statement needs one, that is `contested` with a reason -- not a proof.\n"
    )
    for skill in skills or []:
        parts.append(f"\n---\n\n{skill.strip()}\n")
    return "\n".join(parts)


def render_evidence(evidence: str, *, attempt: int = 1) -> list[str]:
    """The evidence section.  A marker prefix (:data:`EVIDENCE_HEADINGS`) means the
    orchestrator reopened the node and is saying why; anything else is the previous
    attempt's own failure and gets the one piece of advice that applies to all of them."""
    text = evidence.strip()
    for marker, (title, advice) in EVIDENCE_HEADINGS.items():
        if text.startswith(marker):
            if marker == ADJUDICATED_MARKER and REVIEWED_TAIL in text:
                title, advice = REVIEWED_HEADING  # reviewed after failed attempts: it never contested
            body = text[len(marker):].strip()
            return [f"## {title}\n", "```\n" + body[:EVIDENCE_LIMIT] + "\n```\n", advice]
    where = f"attempt {attempt - 1}" if attempt > 1 else "the previous run"
    return [
        f"## What went wrong last time ({where})\n",
        "```\n" + text[:EVIDENCE_LIMIT] + "\n```\n",
        "Do not repeat the same approach. If the evidence shows a resource was "
        "consumed too early, restructure the destructuring rather than trying the "
        "same tactic again.\n",
    ]


def render_library(paths: Iterable[str | Path]) -> str:
    """Name every granted directory and its files: naming a resource is not making it reachable."""
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
        for entry in _library_files(directory):
            lines.append(f"    - `{entry}`")
    lines.append("")
    return "\n".join(lines)


def _library_files(directory: Path) -> list[Path]:
    try:
        entries = sorted(p for p in directory.rglob("*") if p.is_file())
    except OSError:
        return []
    return [p for p in entries if p.name not in ("README.md", "LIBRARY.md")][:LIBRARY_LISTING]


def _library_note(path: Path) -> str:
    for name in ("README.md", "LIBRARY.md"):
        readme = path / name
        if readme.exists():
            for line in read_text(readme).splitlines():
                stripped = line.strip().lstrip("#").strip()
                if stripped:
                    return stripped[:200]
    return ""


def default_docs(index_path: str | Path | None = None) -> list[tuple[str, str]]:
    """Local documentation a worker can reach with no network: the index (if given and
    present) and the Iris sources from the configured library roots.  ``index_path``
    must be absolute -- library code never resolves against the current directory."""
    out: list[tuple[str, str]] = []
    if index_path is not None:
        index = Path(index_path)
        if not index.is_absolute():
            raise ValueError(f"index_path must be absolute, got {index}")
        if index.exists():
            out.append(("every declaration in Iris and std++, one per line", str(index)))
    root = iris_root()
    if root is not None:
        out.append(("the Iris and std++ sources themselves", str(root)))
    return out
