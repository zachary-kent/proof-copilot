"""Findings from the first spec-only ladder run (2026-09-04): two protocol-tolerance
gaps that each cost a design round, and an outage rule that mislabelled a result."""

from __future__ import annotations

import json
from pathlib import Path

from pcp.orch.decomposer import parse_payload, validate_proposal
from pcp.orch.prove import DesignFailed, OrchestrationRequired


def test_a_child_statement_under_the_text_key_is_accepted() -> None:
    """Round 3 of seqlock_design put every child under `text` (the key definitions use)."""
    payload = {
        "children": [
            {"name": "hist_map_snap_lookup", "text": "Lemma hist_map_snap_lookup (k : nat) : k = k."},
            {"name": "other", "statement": "Lemma other : True."},
        ]
    }
    proposal = parse_payload(payload)
    assert [c.name for c in proposal.children] == ["hist_map_snap_lookup", "other"]
    assert proposal.children[0].statement.startswith("Lemma hist_map_snap_lookup")
    assert validate_proposal(proposal) == []


def test_a_definitions_only_repair_is_completed_from_the_base_before_validation() -> None:
    """Round 2 of seqlock_design repaired the definitions and said the children were
    unchanged; the validator rejected it as a plan with no children."""
    base = parse_payload({
        "definitions": [{"name": "value", "text": "Definition value : nat := 0."}],
        "children": [{"name": "c1", "statement": "Lemma c1 : True."}],
    })
    repair = parse_payload({"definitions": [{"name": "value", "text": "Definition value : nat := 1."}]})
    assert validate_proposal(repair)  # alone it is not a plan
    merged = repair.merged_over(base)
    assert [c.name for c in merged.children] == ["c1"]
    assert merged.definitions[-1].text.endswith(":= 1.")
    assert validate_proposal(merged) == []


def test_the_decomposer_merges_a_repair_over_its_base_before_validating(tmp_path: Path) -> None:
    from pcp.orch.decomposer import Decomposer
    from pcp.orch.graph import Graph
    from pcp.orch.model import Node, node_id
    from pcp.orch.protocol import NodeResult
    from pcp.rocq.assemble import Development

    src = tmp_path / "D.v"
    src.write_text("Definition value : nat := 0.\nLemma root : True.\nProof.\nAdmitted.\n", encoding="utf-8")
    graph = Graph(tmp_path / "g.db")
    root = graph.add_node(Node(id=node_id("root"), name="root", statement="Lemma root : True.", statement_status="frozen", rank="root"))
    base = parse_payload({
        "definitions": [{"name": "value", "text": "Definition value : nat := 0."}],
        "children": [{"name": "c1", "statement": "Lemma c1 : 1 = 1."}],
    })
    dec = Decomposer(None, graph, Development(src), tmp_path / "work", None)
    answer = json.dumps({"definitions": [{"name": "value", "text": "Definition value : nat := 1."}]})
    result = NodeResult(status="qed", raw=answer, trace={"final_text": answer})
    out = dec._triage(root, result, attempt_id=graph.start_attempt(root.id, runner="mock", owner="human", role="decomposer"), round_no=2, base=base)
    assert out.ok, out.problems
    assert out.proposal is not None and [c.name for c in out.proposal.children] == ["c1"]
    graph.close()


def test_design_failure_after_running_is_a_result_not_a_usage_error() -> None:
    assert issubclass(DesignFailed, OrchestrationRequired)
    assert DesignFailed("x").exit_code == 1
    assert OrchestrationRequired("x").exit_code == 2


def test_a_run_that_spent_its_design_rounds_is_not_an_outage(tmp_path: Path) -> None:
    from eval.ladder import outage_of
    from pcp.orch.record import AttemptRecord, Recorder

    rec = Recorder(tmp_path / "rec")
    rec.write(AttemptRecord(run_id=rec.run_id, node="root", lemma="root", attempt=1, runner="claude", status="stuck",
                            solved=False, elapsed_s=900.0, evidence="decomposition rejected: child 'x' has no statement"),
              suffix="decompose")
    assert outage_of(exit_code=2, timed_out=False, spawn_error="", record_dir=tmp_path / "rec") == ""
    assert outage_of(exit_code=1, timed_out=False, spawn_error="", record_dir=tmp_path / "rec") == ""
    assert "refused to start" in outage_of(exit_code=2, timed_out=False, spawn_error="", record_dir=tmp_path / "nothing")


def test_every_claude_run_raises_the_cli_output_ceiling(monkeypatch, tmp_path: Path) -> None:
    """seqlock_wf_design: the decomposer's reply overran the CLI's 64k default and was lost."""
    from pcp.config import env as penv
    from pcp.orch.runners import cli as rcli
    from pcp.orch.runners.sandbox import Sandbox

    monkeypatch.delenv(penv.CLAUDE_MAX_OUTPUT_TOKENS, raising=False)
    assert penv.with_runner_defaults({})[penv.CLAUDE_MAX_OUTPUT_TOKENS] == penv.DEFAULT_CLAUDE_MAX_OUTPUT_TOKENS
    assert penv.with_runner_defaults({penv.CLAUDE_MAX_OUTPUT_TOKENS: "9"})[penv.CLAUDE_MAX_OUTPUT_TOKENS] == "9"
    assert penv.CLAUDE_MAX_OUTPUT_TOKENS in penv.SANDBOX_PASSTHROUGH

    seen: dict[str, object] = {}

    async def fake_run_async(argv, **kw):
        seen["env"] = kw.get("env")
        from pcp.util.proc import Streamed

        return Streamed(list(argv), returncode=1)

    monkeypatch.setattr(rcli, "run_async", fake_run_async)
    runner = rcli.claude_headless_runner()
    (tmp_path / "TASK.md").write_text("x", encoding="utf-8")
    import asyncio

    from pcp.orch.protocol import NodePayload

    asyncio.run(rcli.run_cli(runner, NodePayload(node_id="n", name="n", statement="Lemma n : True.", file="f.v", workdir=tmp_path)))
    assert seen["env"][penv.CLAUDE_MAX_OUTPUT_TOKENS] == penv.DEFAULT_CLAUDE_MAX_OUTPUT_TOKENS
    sb = Sandbox(ro_paths=(), masked=(), credentials=(), binaries=(), home=tmp_path)
    assert sb.environment({"PATH": "/bin"})[penv.CLAUDE_MAX_OUTPUT_TOKENS] == penv.DEFAULT_CLAUDE_MAX_OUTPUT_TOKENS


def test_the_glue_rationale_reaches_the_root_prover(tmp_path: Path) -> None:
    """seqlock_wf_design: the decomposer explained how the parent follows from the
    children, and the root packet never showed it."""
    from pcp.orch.contract import DesignContract
    from pcp.orch.graph import Graph
    from pcp.orch.model import Node, node_id
    from pcp.orch.packet import build_packet
    from pcp.orch.prove import ProveConfig
    from pcp.orch.prove.design import adopt_proposal
    from pcp.orch.schedule import siblings_of
    from pcp.rocq.assemble import Development

    src = tmp_path / "D.v"
    src.write_text("Lemma root : True.\nProof.\nAdmitted.\n", encoding="utf-8")
    dev = Development(src)
    graph = Graph(tmp_path / "g.db")
    root = graph.add_node(Node(id=node_id("root"), name="root", statement="Lemma root : True.", statement_status="frozen", rank="root"))
    proposal = parse_payload({
        "children": [{"name": "c1", "statement": "Lemma c1 : 1 = 1."}],
        "glue_rationale": "Deposit the atomic update at the load of the version; collect Q in the failure branch.",
    })
    cfg = ProveConfig(file=src, target="root", workroot=tmp_path / "work", contract=DesignContract.everything_frozen())
    adopt_proposal(cfg, graph, dev, root, proposal)
    root = graph.require(root.id)
    assert root.intent.startswith("Deposit the atomic update")
    paths = build_packet(graph, root, dev, siblings_of(graph, dev), anchor="root", root=tmp_path / "work", attempt_id=1)
    task = paths.task.read_text(encoding="utf-8")
    assert "## Why this lemma exists" in task and "Deposit the atomic update" in task
    graph.close()


def test_standing_contested_and_exhausted_nodes_count_as_design_failures(tmp_path: Path) -> None:
    """A resumed run whose single dispatched node proved still has the design's business
    to finish when a contested child and an attempt-exhausted child sit in the graph."""
    from pcp.orch.graph import Graph
    from pcp.orch.model import Node, node_id
    from pcp.orch.prove.design import design_failed, standing_failures
    from pcp.orch.schedule import NodeOutcome, RunReport

    g = Graph(tmp_path / "g.db")
    for name, status in (("root", "gated"), ("c_contested", "contested"), ("c_spent", "stuck"), ("c_live", "stuck")):
        g.add_node(Node(id=node_id(name), name=name, statement=f"Lemma {name} : True.", statement_status="frozen",
                        rank="root" if name == "root" else "local"))
        if status != "open":
            g.set_proof_status(node_id(name), "claimed")
            if status == "gated":
                g.record_proof(node_id(name), "exact I.")
            else:
                g.set_proof_status(node_id(name), status, evidence=f"{name} evidence")
    for _ in range(2):
        aid = g.start_attempt(node_id("c_spent"), runner="mock", owner="human")
        g.finish_attempt(aid, status="stuck")
    aid = g.start_attempt(node_id("c_live"), runner="mock", owner="human")
    g.finish_attempt(aid, status="stuck")
    report = RunReport(outcomes=[NodeOutcome(node_id=node_id("root"), name="root", status="qed")])
    assert not design_failed(report)
    standing = standing_failures(g, report, max_attempts=2)
    assert sorted(o.name for o in standing.outcomes) == ["c_contested", "c_spent"]  # c_live still has an attempt
    assert design_failed(RunReport.combined([report, standing]))
    g.close()


def test_a_definition_under_a_synonym_key_is_accepted() -> None:
    """Round 4 of the spec-only seqlock_wf run wrote `coq` for its definitions and lost the round."""
    proposal = parse_payload({
        "definitions": [{"name": "tk20", "coq": "Definition tk20 (k : nat) : Prop := k = k."},
                        {"name": "cp21", "code": "Definition cp21 : Prop := True."}],
        "children": [{"name": "n60", "coq": "Lemma n60 : True."}],
    })
    assert [d.name for d in proposal.definitions] == ["tk20", "cp21"]
    assert proposal.children[0].statement.startswith("Lemma n60")


def test_a_child_that_restates_the_root_is_dropped_not_fatal(tmp_path: Path) -> None:
    """Round 5 of the spec-only seqlock_wf run listed the proved root among its children
    and lost the whole revision to it."""
    from pcp.orch.decomposer import drop_redundant_children
    from pcp.orch.model import Node, node_id
    from pcp.rocq.assemble import Development

    src = tmp_path / "D.v"
    src.write_text("Lemma helper : True.\nProof. exact I. Qed.\nLemma root : 1 = 1.\nProof.\nAdmitted.\n", encoding="utf-8")
    root = Node(id=node_id("root"), name="root", statement="Lemma root : 1 = 1.", statement_status="frozen", rank="root")
    proposal = parse_payload({"children": [
        {"name": "root", "statement": "Lemma root : 1 = 1."},
        {"name": "helper", "statement": "Lemma helper : True."},
        {"name": "same_as_root", "statement": "Lemma same_as_root : 1 = 1."},
        {"name": "c_new", "statement": "Lemma c_new : 2 = 2."},
    ]})
    kept, notes = drop_redundant_children(Development(src), root, proposal)
    assert [c.name for c in kept.children] == ["c_new"]
    assert len(notes) == 3 and all("dropped child" in n for n in notes)
    assert validate_proposal(kept) == []
    # Nothing left is still a problem the validator reports (a plan with no children).
    only_root = parse_payload({"children": [{"name": "root", "statement": "Lemma root : 1 = 1."}]})
    empty, _ = drop_redundant_children(Development(src), root, only_root)
    assert validate_proposal(empty)


def test_a_repair_reask_uses_the_approver_and_is_not_a_design_round(tmp_path: Path) -> None:
    """Round 6 of the spec-only seqlock_wf run was a 16-minute redesign spent on one
    syntax error in a child statement."""
    import asyncio

    from pcp.orch.decomposer import Decomposer
    from pcp.orch.graph import Graph
    from pcp.orch.model import Node, node_id
    from pcp.orch.protocol import NodeResult
    from pcp.orch.prove.design import design_rounds_used
    from pcp.rocq.assemble import Development

    class Scripted:
        def __init__(self, name, text):
            self.name, self.text, self.calls = name, text, 0

        def available(self):
            return True

        async def run_node(self, node):
            self.calls += 1
            return NodeResult(status="qed", raw=self.text, trace={"final_text": self.text, "model": self.name})

    src = tmp_path / "D.v"
    src.write_text("Lemma root : True.\nProof.\nAdmitted.\n", encoding="utf-8")
    graph = Graph(tmp_path / "g.db")
    root = graph.add_node(Node(id=node_id("root"), name="root", statement="Lemma root : True.", statement_status="frozen", rank="root"))
    fixed = json.dumps({"children": [{"name": "c1", "statement": "Lemma c1 : 1 = 1."}]})
    decomposer, approver = Scripted("decomposer", fixed), Scripted("approver", fixed)
    d = Decomposer(decomposer, graph, Development(src), tmp_path / "work", None, approver=approver)
    out = asyncio.run(d.amend(root, evidence="Syntax error in c1", round_no=2, budget_seconds=5, kind="design", repair=True))
    assert out.ok and approver.calls == 1 and decomposer.calls == 0
    assert graph.attempts_for(root.id)[-1]["role"] == "repairer"
    assert design_rounds_used(graph, root) == 0, "a repair never counts as a design round"
    graph.close()


def test_an_entry_whose_text_hides_under_any_vernacular_valued_key_is_read() -> None:
    """Round 7 wrote `statement` for its definitions (mirroring the children)."""
    p = parse_payload({
        "definitions": [{"name": "tk", "statement": "Definition tk : Prop := True.", "notes": "receipt"},
                        {"name": "wl", "decl": "Definition wl : Prop := True."}],
        "children": [{"name": "c", "obligation": "Lemma c : True."}],
    })
    assert [d.name for d in p.definitions] == ["tk", "wl"] and p.children[0].name == "c"
