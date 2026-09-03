"""The runner interface: ~30 lines of contract, many implementations (PLAN.md 11).

"Own the graph, rent the runner."  The obligation graph is specific to this problem
and must survive process death, so it is ours.  Running one node attempt is
commodity, so it sits behind this protocol and can be A/B'd empirically instead of
bet on up front.

A prover returns exactly one of three shapes -- ``qed`` / ``contested`` / ``stuck`` --
never a partial edit and **never a statement**.  A prover that needs a lemma files a
request; the request routes through the statement pipeline before anyone proves it.
That is what stops an unaudited shadow-spec ecosystem from growing (PLAN.md 8.3).
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Protocol

Status = ("qed", "contested", "stuck", "error")


@dataclass
class LemmaRequest:
    """A prover asking for a lemma it cannot state itself."""

    statement: str
    rationale: str = ""

    def to_json(self) -> dict[str, str]:
        return {"statement": self.statement, "rationale": self.rationale}


@dataclass
class NodePayload:
    """The deterministic context packet handed to a prover (PLAN.md 8.6).

    Everything here is computed, not narrated: the frozen statement, the file it
    lives in, the siblings it may cite as admitted stubs, the intent brief that keeps
    a deep node speaking the root's idiom, and evidence from the previous attempt.
    """

    node_id: str
    name: str
    statement: str
    file: str
    workdir: Path
    #: The assembled `.v` the worker edits the body of.
    scratch_file: str = "node.v"
    intent: str = ""
    siblings: list[tuple[str, str]] = field(default_factory=list)
    premises: list[str] = field(default_factory=list)
    #: Blame trace / gate output from the previous attempt, for the one retry.
    evidence: str = ""
    budget_seconds: float = 900.0
    tier: str = ""
    attempt: int = 1
    skills: list[str] = field(default_factory=list)
    check_command: str = "pcp check"


@dataclass
class NodeResult:
    status: str
    proof: str = ""
    evidence: str = ""
    requests: list[LemmaRequest] = field(default_factory=list)
    cost: dict[str, Any] = field(default_factory=dict)
    raw: str = ""
    elapsed_s: float = 0.0
    #: What the worker actually did: turns, tool calls, tokens, and the errors it
    #: fought through.  Present for runners that stream their events; empty for the
    #: ones that only report a final message.
    trace: dict[str, Any] = field(default_factory=dict)

    @property
    def ok(self) -> bool:
        return self.status == "qed" and bool(self.proof.strip())


class Runner(Protocol):
    """One node attempt.  Implementations must not raise for ordinary failure."""

    name: str

    async def run_node(self, node: NodePayload) -> NodeResult: ...

    def available(self) -> bool: ...


# ------------------------------------------------------------------ result parsing

_FENCE = re.compile(r"```(?:coq|rocq|v)?\s*\n(.*?)```", re.S)
_ANSWER_FILE = "answer.json"
_PROOF_FILE = "proof.v"
_NODE_FILE = "pcp-node.json"


def read_result(workdir: Path, stdout: str) -> NodeResult:
    """Read a worker's answer, most-structured source first.

    Three channels because one-shot CLI runners have no mid-flight protocol and the
    cheap tier is not reliable about format: a JSON file if it wrote one, a bare
    proof file if it wrote that, and a fenced block in the transcript as the last
    resort.  A worker that produced a proof but garbled the wrapper still counts.
    """
    answer = workdir / _ANSWER_FILE
    if answer.exists():
        try:
            data = json.loads(answer.read_text(encoding="utf-8"))
            return NodeResult(
                status=str(data.get("status", "stuck")),
                proof=str(data.get("proof", "")),
                evidence=str(data.get("evidence", "")),
                requests=[
                    LemmaRequest(statement=r.get("statement", ""), rationale=r.get("rationale", ""))
                    for r in data.get("requests", [])
                    if isinstance(r, dict)
                ],
                raw=stdout[-4000:],
            )
        except (json.JSONDecodeError, TypeError, AttributeError) as exc:
            return NodeResult(status="stuck", evidence=f"malformed {_ANSWER_FILE}: {exc}", raw=stdout[-4000:])

    proof = workdir / _PROOF_FILE
    if proof.exists() and proof.read_text(encoding="utf-8").strip():
        return NodeResult(status="qed", proof=proof.read_text(encoding="utf-8").strip(), raw=stdout[-4000:])

    blocks = _FENCE.findall(stdout or "")
    if blocks:
        return NodeResult(status="qed", proof=blocks[-1].strip(), raw=stdout[-4000:])

    # Fourth channel: the assembled `.v` the worker was told to edit in place.  A
    # worker killed at its deadline has usually written its proof *there* and
    # nowhere else, and PLAN.md 6 says the kill is followed by a requeue "with the
    # partial trace as evidence" -- which is worth nothing if the partial is dropped
    # on the floor.
    edited = read_edited_body(workdir)
    if edited:
        return NodeResult(
            status="stuck",
            proof=edited,
            evidence="recovered a partial proof from the worker's edited file; it wrote no answer.json",
            raw=stdout[-4000:],
        )

    return NodeResult(
        status="stuck",
        evidence="the worker produced no answer.json, no proof.v and no fenced proof block",
        raw=stdout[-4000:],
    )


def read_edited_body(workdir: Path) -> str:
    """The target lemma's proof body, as the worker left it in the assembled file.

    Returns "" when the body is still the untouched `admit.` placeholder -- an
    unedited stub is not partial progress, and reporting it as such would make a
    worker that did nothing look like one that got close.
    """
    node_file = workdir / _NODE_FILE
    if not node_file.exists():
        return ""
    try:
        target = json.loads(node_file.read_text(encoding="utf-8")).get("target")
    except (json.JSONDecodeError, OSError):
        return ""
    if not target:
        return ""
    from pcp.core.vernac import find_block

    for candidate in sorted(workdir.glob("*.v")):
        try:
            source = candidate.read_text(encoding="utf-8")
        except OSError:
            continue
        block = find_block(source, target)
        if block is None or not block.has_proof:
            continue
        body = block.body(source).strip()
        if not body or body in ("admit.", "Admitted.", "admit"):
            continue
        return body
    return ""


def strip_proof_wrapper(text: str) -> str:
    """Accept a body with or without its `Proof.`/`Qed.` wrapper.

    Workers wrap inconsistently and the assembler supplies the wrapper itself; a
    duplicated `Proof.` is a compile error that has nothing to do with the proof.
    """
    body = text.strip()
    body = re.sub(r"^\s*Proof\s*(?:using[^.]*)?\.\s*", "", body)
    body = re.sub(r"\s*(?:Qed|Defined|Admitted)\s*\.\s*$", "", body)
    return body.strip()
