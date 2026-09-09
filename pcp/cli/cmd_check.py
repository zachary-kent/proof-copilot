"""``pcp check`` -- the worker's gate, run inside a node workdir (contract §1.2).

"It compiled for me" and "it passed the gate" must be the same sentence: this runs
the identical per-node shape the orchestrator runs (siblings stubbed, the file
truncated after the anchor, the prefix's other proofs admitted, the plan preamble
inserted), so what the worker debugs is what the gate judges.

The petanque replay diagnosis is opt-in per packet (``pcp-node.json:diagnose``)
because the replay *is* the state layer: a control arm denied the tools must not get
them back through the checker.  It runs only when a compile actually ran and
failed, and it never makes the check fail.
"""

from __future__ import annotations

import argparse
import inspect
import sys
from pathlib import Path
from typing import Any

from pcp.cli.common import absolute, err, read_body_arg
from pcp.errors import UsageError
from pcp.orch.gate import (
    CHECK_AMBIENT,
    CHECK_AXIOMS,
    CHECK_AXIOMS_DESIGN,
    CHECK_COMPILES,
    CHECK_CONTRACT,
    CHECK_ESCAPE,
    CHECK_NO_ADMIT,
    CHECK_PINNING,
    CHECK_PROOF_USING,
    CHECK_STRUCTURE,
    Gate,
    GateResult,
)
from pcp.orch.protocol import NODE_FILE, PROOF_FILE
from pcp.rocq.assemble import Development, NodeSpec
from pcp.rocq.body import strip_proof_wrapper
from pcp.rocq.decls import find_block
from pcp.util.io import json_dumps, json_load, read_text

#: Machine scratch (statements-only twins, replay twins): never a worker's file.
SCRATCH_INFIX = "__pcp"
DIAGNOSIS_BUDGET_S = 90.0
DIAGNOSIS_MAX_TACTICS = 400

#: What a failing check means, in the worker's terms.  Keyed on the gate's own
#: check-name constants, so a renamed check cannot silently lose its advice.
CHECK_ADVICE: dict[str, str] = {
    CHECK_NO_ADMIT: (
        "Your body contains an admit. The gate rejects it before compiling anything. "
        "If you genuinely cannot finish, answer `stuck` with evidence instead."
    ),
    CHECK_ESCAPE: "Your body disables a kernel check. Remove it; the proof has to hold with the checks on.",
    CHECK_AMBIENT: (
        "Global registrations change how *future* statements elaborate. Make it "
        "`Local` (Local Ltac / Local Instance / Local Hint)."
    ),
    CHECK_PINNING: (
        "The frozen statement is not present verbatim. You changed the lemma line -- "
        "revert it; only the proof body is yours."
    ),
    CHECK_PROOF_USING: "The assembled file lost its `Set Default Proof Using` directive.",
    CHECK_STRUCTURE: (
        "Your body is not a single proof: it ends the proof early, opens another one, or "
        "declares something. Send exactly the tactics between `Proof.` and `Qed.`."
    ),
    CHECK_COMPILES: "Rocq rejected the proof. The first error is above; the rest of the output is in the same report.",
    CHECK_CONTRACT: (
        "You changed something the contract does not let you change. The program and "
        "the specifications are the theorem; only the definitions named in the "
        "contract are yours. Imports may be added but not removed."
    ),
    CHECK_AXIOMS: (
        "The proof leans on an axiom that is not allowed. Sibling lemmas still stubbed "
        "with Admitted are fine; anything else is not."
    ),
    CHECK_AXIOMS_DESIGN: "The development leans on an axiom that is not allowed.",
}


def worker_files(workdir: Path) -> list[Path]:
    return sorted(p for p in workdir.glob("*.v") if SCRATCH_INFIX not in p.stem)


def body_from_workdir(workdir: Path, meta: dict[str, Any]) -> str | None:
    """Body resolution (§1.2): the packet's own scratch file first, then any other
    worker ``.v`` holding the target, then ``proof.v``, then ``body.v``."""
    target = str(meta.get("target", ""))
    candidates: list[Path] = []
    scratch = meta.get("scratch")
    if scratch and (workdir / str(scratch)).exists():
        candidates.append(workdir / str(scratch))
    candidates += [p for p in worker_files(workdir) if p not in candidates]
    for path in candidates:
        source = read_text(path)
        block = find_block(source, target)
        if block is not None and block.has_proof:
            return block.body(source)
    for name in (PROOF_FILE, "body.v"):
        path = workdir / name
        if path.exists():
            return read_text(path)
    return None


def candidate_file(workdir: Path, dev: Development) -> str | None:
    local = workdir / dev.path.name
    if local.exists():
        return read_text(local)
    for path in worker_files(workdir):
        return read_text(path)
    return None


def check_advice(result: GateResult) -> str:
    lines = ["what to do:"]
    for check in result.checks:
        if check.ok or check.advisory:
            continue
        advice = CHECK_ADVICE.get(check.name)
        lines.append(f"  · {check.name}: {advice or check.detail or 'see the report above'}")
    if len(lines) == 1:
        lines.append("  · every named check passed; re-read the compiler output above")
    return "\n".join(lines)


def wants_diagnosis(meta: dict[str, Any], explicit: bool | None) -> bool:
    return bool(explicit) if explicit is not None else bool(meta.get("diagnose"))


def compile_ran_and_failed(result: GateResult) -> bool:
    return any(c.name == CHECK_COMPILES and not c.ok and not c.detail.startswith("skipped") for c in result.checks)


def diagnose_failure(result: GateResult, meta: dict[str, Any], dev: Development, body: str, explicit: bool | None) -> str:
    """The petanque replay, lazily and never fatally (module docstring)."""
    if result.ok or not wants_diagnosis(meta, explicit):
        return ""
    if not compile_ran_and_failed(result) or not result.assembled:
        return ""
    try:
        from pcp.state.explain import explain
    except ImportError as exc:
        return f"(diagnosis unavailable: {exc})" if explicit else ""
    kwargs: dict[str, Any] = {
        "assembly_text": result.assembled,
        "assembled_path_name": dev.path.name,
        "compile_result": result.compile_output,
        "compile_output_or_result": result.compile_output,
        "dev": dev,
        "root": dev.root,
        "target": str(meta.get("target", "")),
        "body": body,
        "budget_seconds": DIAGNOSIS_BUDGET_S,
        "max_tactics": DIAGNOSIS_MAX_TACTICS,
    }
    try:
        accepted = set(inspect.signature(explain).parameters)
        text = explain(**{k: v for k, v in kwargs.items() if k in accepted})
    except Exception as exc:  # noqa: BLE001 -- best effort by construction
        return f"(diagnosis unavailable: {type(exc).__name__}: {exc})" if explicit else ""
    if not text and explicit:
        return "(no diagnosis: petanque is not on PATH, or the failure is not inside a proof body)"
    return str(text or "")


def _print(result: GateResult, diagnosis: str, *, as_json: bool, extra: str = "") -> None:
    if as_json:
        payload = result.to_json()
        if diagnosis:
            payload["diagnosis"] = diagnosis
        print(json_dumps(payload))
        return
    print(result.render())
    if diagnosis:
        print()
        print(diagnosis)
    if extra:
        print()
        print(extra)
    if not result.ok:
        print()
        print(check_advice(result))


def cmd_check(args: argparse.Namespace) -> int:
    workdir = absolute(args.dir)
    assert workdir is not None
    meta_path = workdir / NODE_FILE
    if not meta_path.exists():
        err(
            f"no {NODE_FILE} in {workdir}.\n"
            "Run `pcp check` from inside your node's work directory (the one holding "
            "TASK.md), or pass --dir. With no arguments it checks the proof body as "
            "you left it in the .v file; `pcp check proof.v` checks a body from a file."
        )
        return 2
    meta = json_load(meta_path)
    positional = getattr(args, "body_positional", None)
    body_arg = args.body
    if positional is not None:
        if body_arg is not None and str(body_arg) != str(positional):
            raise UsageError(f"give the body once: BODY {positional} and --body {body_arg} disagree")
        body_arg = Path(positional)

    dev_path = Path(str(meta.get("file") or ""))
    if not dev_path.is_file():
        raise UsageError(
            f"{dev_path or '<unset>'}: the development this packet was assembled against is gone "
            f"({NODE_FILE}:file). The run that wrote it was probably started over with --fresh."
        )
    dev = Development(dev_path)
    gate = Gate(dev)
    preamble = str(meta.get("preamble", "") or "")

    if args.design:
        from pcp.orch.contract import DesignContract

        candidate = candidate_file(workdir, dev)
        if candidate is None:
            err(f"no {dev.path.name} in {workdir} to check")
            return 2
        corpus = Path(meta.get("corpus") or dev.path.parent)
        contract: Any = DesignContract.from_corpus(corpus) if corpus.is_dir() else DesignContract.everything_frozen()
        result = gate.run_design(candidate, contract)
        diagnosis = diagnose_failure(result, meta, dev, "", args.diagnose)
        _print(result, diagnosis, as_json=args.json, extra=f"contract: {contract.describe()}")
        return 0 if result.ok else 1

    body = read_body_arg(body_arg) if body_arg is not None else body_from_workdir(workdir, meta)
    if body is None:
        err("could not find your proof body. Either edit the assembled .v in this directory, or pass --body proof.v")
        return 2
    body = strip_proof_wrapper(body)
    target, anchor = str(meta["target"]), str(meta["anchor"])
    specs = [
        NodeSpec(str(s["name"]), str(s["statement"]), None)
        for s in meta.get("siblings", [])
        if s["name"] != target
    ]
    is_anchor = target == anchor
    if not is_anchor:
        specs.append(NodeSpec(target, str(meta["statement"]), body))
    result = gate.run(
        anchor, specs,
        target=target, target_body=body if is_anchor else None,
        unused_premise_report=bool(args.unused_premises), stub_prefix=not args.full,
        extra_preamble=preamble,
    )
    diagnosis = diagnose_failure(result, meta, dev, body, args.diagnose)
    _print(result, diagnosis, as_json=args.json)
    sys.stdout.flush()
    return 0 if result.ok else 1
