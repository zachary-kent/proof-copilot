"""The worker protocol: what a prover receives, what it returns, how it is read.

A prover returns exactly one of three shapes -- ``qed`` / ``contested`` / ``stuck`` --
never a partial edit and **never a statement** (PLAN.md 8.6).  A fourth status,
``error``, is reserved for the *infrastructure*: a missing binary, a revoked login, a
provider outage.  It is never retried and never blamed on the worker.

Every attempt reads from its **own** directory (``NodePayload.workdir``), created
fresh for that attempt, so nothing a previous attempt or run left behind can be
mistaken for the current answer.
"""

from __future__ import annotations

import json
import os
import re
import stat
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Protocol

from pcp.rocq.body import is_placeholder, strip_proof_wrapper
from pcp.rocq.decls import find_block
from pcp.util.io import read_text

STATUSES: tuple[str, ...] = ("qed", "contested", "stuck", "error")

ANSWER_FILE = "answer.json"
PROOF_FILE = "proof.v"
NODE_FILE = "pcp-node.json"
TASK_FILE = "TASK.md"
#: A worker file larger than this is not an answer.
MAX_WORKER_FILE_BYTES = 8 << 20
#: A prover that needs more than this many definition changes is contesting the design.
MAX_AMENDMENTS_PER_ANSWER = 8
#: Evidence prefixes the packet turns into a heading: a node reopened because a
#: definition changed, or because an approver read its contest and sent it back.
AMENDED_MARKER = "AMENDED:"
ADJUDICATED_MARKER = "ADJUDICATED:"


def unreadable_reason(path: Path) -> str:
    """Why ``path`` may not be read as a worker file; ``""`` when it may.

    Only a regular file (no symlink) below :data:`MAX_WORKER_FILE_BYTES` is read.  A
    FIFO or a symlink to ``/dev/zero`` named ``answer.json`` blocked the orchestrator
    forever, and a directory named ``proof.v`` made the runner raise -- a worker must
    not be able to do either (review finding).
    """
    try:
        st = os.lstat(path)
    except FileNotFoundError:
        return "missing"
    except OSError as exc:
        return f"unreadable ({exc.strerror})"
    if stat.S_ISLNK(st.st_mode):
        return "a symlink, not a file"
    if not stat.S_ISREG(st.st_mode):
        return "not a regular file"
    if st.st_size > MAX_WORKER_FILE_BYTES:
        return f"{st.st_size} bytes, over the {MAX_WORKER_FILE_BYTES}-byte limit"
    return ""


@dataclass
class LemmaRequest:
    """A prover asking for a lemma it cannot state itself."""

    statement: str
    rationale: str = ""

    def to_json(self) -> dict[str, str]:
        return {"kind": "lemma", "statement": self.statement, "rationale": self.rationale}

    @classmethod
    def from_json(cls, d: Any) -> LemmaRequest | None:
        if not isinstance(d, dict):
            return None
        statement = str(d.get("statement", "")).strip()
        if not statement:
            return None
        return cls(statement=statement, rationale=str(d.get("rationale", "")))


@dataclass
class AmendmentRequest:
    """A prover asking for a *definition* to change -- the incremental route back to
    the design (PLAN.md 8.5, 9.2).

    Mid-proof a prover discovers the invariant lacks a fact or a modality guard (the
    registry entry stored ``Q`` where the close site needs ``▷ Q``).  Contesting the
    statement buys a full design revision for a one-conjunct change; this asks for
    exactly the conjunct.  ``add`` is a pure strengthening (machine-checked, applied
    mechanically when it compiles); ``replace`` is the complete new ``Definition``
    sentence and needs an approver.  A prover still never *writes* the design: the
    request is applied by the orchestrator against the contract, and everything it
    touches is replayed.
    """

    definition: str
    add: str = ""
    replace: str = ""
    at: str = ""
    why: str = ""
    #: The requesting node's name, filled by the scheduler.
    requester: str = ""

    @property
    def kind(self) -> str:
        return "add" if self.add.strip() else "replace"

    @property
    def text(self) -> str:
        return self.add.strip() if self.kind == "add" else self.replace.strip()

    def key(self) -> str:
        """Dedupe key: two provers asking for the same conjunct is one amendment."""
        return f"{self.definition.strip()}::{self.kind}::{' '.join(self.text.split())}"

    def describe(self) -> str:
        """``d15: + ▷ Q`` / ``d15: replaced``."""
        return f"{self.definition}: + {' '.join(self.add.split())}" if self.kind == "add" else f"{self.definition}: replaced"

    def to_json(self) -> dict[str, str]:
        return {
            "kind": "amend", "definition": self.definition, "add": self.add, "replace": self.replace,
            "at": self.at, "why": self.why, "requester": self.requester,
        }

    @classmethod
    def from_json(cls, d: Any) -> AmendmentRequest | None:
        """``None`` for anything that is not a usable request; :func:`amendment_problem`
        says why, so a malformed entry is kept in the evidence rather than lost."""
        if amendment_problem(d):
            return None
        return cls(
            definition=str(d["definition"]).strip(),
            add=str(d.get("add") or "").strip(),
            replace=str(d.get("replace") or "").strip(),
            at=str(d.get("at") or "").strip(),
            why=str(d.get("why") or d.get("rationale") or "").strip(),
            requester=str(d.get("requester") or "").strip(),
        )


def amendment_problem(d: Any) -> str:
    """Why ``d`` is not an amendment request (``""`` when it is)."""
    if not isinstance(d, dict):
        return "an amendment must be an object with `definition` and `add` or `replace`"
    if not str(d.get("definition") or "").strip():
        return "amendment without a `definition` name"
    if not str(d.get("add") or "").strip() and not str(d.get("replace") or "").strip():
        return f"amendment of `{str(d.get('definition')).strip()}` with neither `add` nor `replace`"
    return ""


def parse_requests(entries: Any) -> tuple[list[LemmaRequest], list[AmendmentRequest]]:
    """Split a kind-tagged ``requests`` list back into its two kinds (the attempt row
    stores both under one key)."""
    lemmas: list[LemmaRequest] = []
    amendments: list[AmendmentRequest] = []
    for entry in entries or []:
        if isinstance(entry, dict) and entry.get("kind") == "amend":
            amendment = AmendmentRequest.from_json(entry)
            if amendment:
                amendments.append(amendment)
            continue
        lemma = LemmaRequest.from_json(entry)
        if lemma:
            lemmas.append(lemma)
    return lemmas, amendments


@dataclass
class NodePayload:
    """The deterministic context packet handed to a prover (PLAN.md 8.6)."""

    node_id: str
    name: str
    statement: str
    file: str
    #: This attempt's own directory.  Fresh per attempt.
    workdir: Path
    #: The assembled ``.v`` the worker edits the body of.
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
    #: The prompt file the runner feeds the model; defaults to ``TASK.md`` in ``workdir``.
    prompt_file: str = TASK_FILE

    @property
    def prompt_path(self) -> Path:
        return Path(self.workdir) / self.prompt_file


@dataclass
class NodeResult:
    status: str
    proof: str = ""
    evidence: str = ""
    requests: list[LemmaRequest] = field(default_factory=list)
    #: Definition changes the prover asked for (``stuck``/``contested`` answers).
    amendments: list[AmendmentRequest] = field(default_factory=list)
    cost: dict[str, Any] = field(default_factory=dict)
    #: The runner's raw output (the full event stream for streaming runners).
    raw: str = ""
    elapsed_s: float = 0.0
    #: What the worker actually did: turns, tool calls, tokens, errors (``WorkerTrace``).
    trace: dict[str, Any] = field(default_factory=dict)
    #: The runner process's exit code, when there was one.
    exit_code: int | None = None
    timed_out: bool = False

    def __post_init__(self) -> None:
        if self.status not in STATUSES:
            self.status = "stuck"

    @property
    def ok(self) -> bool:
        return self.status == "qed" and bool(self.proof.strip())

    @property
    def model(self) -> str:
        return str(self.trace.get("model", "") or "")

    def to_json(self) -> dict[str, Any]:
        return {
            "status": self.status,
            "proof": self.proof,
            "evidence": self.evidence,
            "requests": [r.to_json() for r in self.requests],
            "amendments": [a.to_json() for a in self.amendments],
            "cost": self.cost,
            "elapsed_s": self.elapsed_s,
            "exit_code": self.exit_code,
            "timed_out": self.timed_out,
        }


class Runner(Protocol):
    """One node attempt.  Implementations never raise for an ordinary failure."""

    name: str

    async def run_node(self, node: NodePayload) -> NodeResult: ...

    def available(self) -> bool: ...


# ------------------------------------------------------------------ result parsing

# A fenced block: the opening fence's language tag is captured so a ```json fence
# cannot be mistaken for the closing fence of a coq block.
_FENCE = re.compile(r"```(?P<lang>[A-Za-z0-9_-]*)[^\n]*\n(?P<body>.*?)```", re.S)
_PROOF_LANGS = {"", "coq", "rocq", "v"}


def fenced_proof_blocks(text: str) -> list[str]:
    """Every ```coq/rocq/v/plain fenced block in ``text``, in order."""
    return [m.group("body") for m in _FENCE.finditer(text or "") if m.group("lang").lower() in _PROOF_LANGS]


def read_answer_file(path: Path) -> NodeResult | None:
    """Parse ``answer.json``; ``None`` if absent."""
    problem = unreadable_reason(path)
    if problem == "missing":
        return None
    if problem:
        return NodeResult(status="stuck", evidence=f"malformed {ANSWER_FILE}: {problem}")
    try:
        data = json.loads(read_text(path))
    except (ValueError, RecursionError, OSError) as exc:
        return NodeResult(status="stuck", evidence=f"malformed {ANSWER_FILE}: {type(exc).__name__}: {exc}"[:400])
    if not isinstance(data, dict):
        return NodeResult(status="stuck", evidence=f"malformed {ANSWER_FILE}: expected a JSON object")
    status = str(data.get("status", "stuck")).strip().lower()
    if status not in ("qed", "stuck", "contested"):
        status = "stuck"
    requests = [r for r in (LemmaRequest.from_json(x) for x in data.get("requests") or []) if r]
    amendments, skipped = _read_amendments(data.get("amendments"))
    proof = data.get("proof", "")
    if not isinstance(proof, str):
        proof = ""
    evidence = str(data.get("evidence", "") or "")
    if skipped:
        evidence = "\n".join(filter(None, [evidence, "ignored amendment request(s): " + "; ".join(skipped)]))
    return NodeResult(
        status=status,
        proof=strip_proof_wrapper(proof),
        evidence=evidence,
        requests=requests,
        amendments=amendments,
    )


def _read_amendments(raw: Any) -> tuple[list[AmendmentRequest], list[str]]:
    """Tolerant: a malformed entry is skipped and the reason kept for the evidence;
    a ``qed`` answer's amendments are irrelevant and dropped by the scheduler."""
    if raw is None:
        return [], []
    if not isinstance(raw, list):
        return [], ["`amendments` must be a list of objects"]
    out: list[AmendmentRequest] = []
    skipped: list[str] = []
    for entry in raw[:MAX_AMENDMENTS_PER_ANSWER]:
        problem = amendment_problem(entry)
        if problem:
            skipped.append(problem)
            continue
        parsed = AmendmentRequest.from_json(entry)
        if parsed is not None:
            # The scheduler names the requester.  A worker that writes another node's
            # name here would have that node told, credited and reopened in its place.
            parsed.requester = ""
            out.append(parsed)
    if len(raw) > MAX_AMENDMENTS_PER_ANSWER:
        skipped.append(f"{len(raw) - MAX_AMENDMENTS_PER_ANSWER} more than the {MAX_AMENDMENTS_PER_ANSWER} an answer may carry")
    return out, skipped


def read_edited_body(workdir: Path, target: str, *, scratch_file: str | None = None) -> str:
    """The target's proof body as the worker left it in the assembled file, else ``""``.

    The packet's own scratch file is consulted first; other ``*.v`` files only after
    it, and machine scratch (``__pcp`` in the stem) never.  The untouched ``admit.``
    placeholder is not partial progress.
    """
    candidates: list[Path] = []
    if scratch_file:
        p = workdir / scratch_file
        if p.exists():
            candidates.append(p)
    for p in sorted(workdir.glob("*.v")):
        if "__pcp" in p.stem or p in candidates:
            continue
        candidates.append(p)
    for candidate in candidates:
        if unreadable_reason(candidate):
            continue
        try:
            source = read_text(candidate)
        except OSError:
            continue
        block = find_block(source, target)
        if block is None or not block.has_proof:
            continue
        body = block.body(source).strip()
        if is_placeholder(body):
            continue
        return body
    return ""


def read_result(workdir: Path, stdout: str, *, target: str | None = None, scratch_file: str | None = None) -> NodeResult:
    """Read a worker's answer from *this attempt's* directory, most-structured source first.

    1. ``answer.json`` (the canonical answer);
    2. ``proof.v`` (a bare proof file) -> ``qed``;
    3. the last fenced proof block in the transcript's final text -> ``qed``;
    4. the target's proof body as edited in the scratch ``.v`` -> ``stuck`` with the
       partial as ``proof`` (a killed worker usually wrote its work there);
    5. nothing -> ``stuck``.
    """
    workdir = Path(workdir)
    answer = read_answer_file(workdir / ANSWER_FILE)
    if answer is not None:
        return answer
    proof_file = workdir / PROOF_FILE
    if not unreadable_reason(proof_file):
        body = strip_proof_wrapper(read_text(proof_file))
        if body:
            return NodeResult(status="qed", proof=body)
    blocks = fenced_proof_blocks(stdout)
    if blocks and blocks[-1].strip():
        return NodeResult(status="qed", proof=strip_proof_wrapper(blocks[-1]))
    if target is None:
        node_file = workdir / NODE_FILE
        if node_file.exists():
            try:
                target = json.loads(read_text(node_file)).get("target")
            except (ValueError, RecursionError, OSError, AttributeError):
                target = None
    if target:
        edited = read_edited_body(workdir, target, scratch_file=scratch_file)
        if edited:
            return NodeResult(
                status="stuck",
                proof=edited,
                evidence="recovered a partial proof from the worker's edited file; it wrote no answer.json",
            )
    return NodeResult(
        status="stuck",
        evidence="the worker produced no answer.json, no proof.v and no fenced proof block",
    )
