"""Graph, sentinels, amendments, decomposition policy, packet, handoff."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from pcp.orch.graph import Budget, Graph, Node


@pytest.fixture()
def graph(tmp_path: Path) -> Graph:
    g = Graph(tmp_path / "g.db")
    yield g
    g.close()


def _node(g: Graph, ident: str, **kw) -> Node:
    return g.add_node(
        Node(
            id=ident,
            name=kw.pop("name", ident),
            statement=kw.pop("statement", f"Lemma {ident} : True."),
            statement_status=kw.pop("statement_status", "frozen"),
            **kw,
        )
    )


# ----------------------------------------------------------------------- graph

def test_the_scheduling_invariant_ignores_depth(graph: Graph) -> None:
    """Every frozen statement with an open proof is dispatchable *now*."""
    _node(graph, "root", rank="root")
    _node(graph, "deep", parent="root", depth=7)
    graph.add_edge("root", "deep")
    assert {n.id for n in graph.frontier()} == {"root", "deep"}


def test_non_mockable_nodes_are_scheduled_first(graph: Graph) -> None:
    _node(graph, "a")
    _node(graph, "blocker", mockable=False)
    assert graph.frontier()[0].id == "blocker"


def test_a_proposed_statement_is_not_dispatchable(graph: Graph) -> None:
    _node(graph, "unfrozen", statement_status="proposed")
    assert graph.frontier() == []


def test_edges_pin_epochs_so_staleness_is_graph_arithmetic(graph: Graph) -> None:
    _node(graph, "a")
    b = _node(graph, "b")
    graph.add_edge("a", "b")
    assert graph.stale_edges("a") == []
    graph.update(b.id, epoch=b.epoch + 1)
    assert graph.stale_edges("a") == [("b", 0, 1)]


def test_budgets_are_vectors_and_split_geometrically() -> None:
    b = Budget(requests=100, tokens=40_000, dollars=8.0, seconds=3600)
    child = b.split(4)
    assert (child.requests, child.tokens, child.dollars) == (25, 10_000, 2.0)


def test_the_graph_survives_process_death(tmp_path: Path) -> None:
    path = tmp_path / "g.db"
    g1 = Graph(path)
    _node(g1, "a", proof_status="gated", body="exact I.")
    g1.close()
    g2 = Graph(path)
    node = g2.get("a")
    assert node is not None and node.proof_status == "gated" and node.body == "exact I."
    g2.close()


def test_every_mutation_is_an_event_for_the_dashboard(graph: Graph) -> None:
    _node(graph, "a")
    graph.set_proof_status("a", "stuck", evidence="because")
    kinds = [e["kind"] for e in graph.events_since(0)]
    assert "node.added" in kinds and "node.proof_status" in kinds


# ------------------------------------------------------------------- sentinels

def test_duplicate_statements_are_blocked_before_anyone_proves_them() -> None:
    from pcp.orch.sentinels import run_free_sentinels

    report = run_free_sentinels({
        "a": "Lemma a (P Q : iProp Σ) : P ∗ Q -∗ Q ∗ P.",
        "b": "Lemma b (P Q : iProp Σ) : P ∗ Q -∗ Q ∗ P.",
    })
    assert not report.ok
    assert any(h.sentinel == "duplicate statement" for h in report.blocking)


def test_a_rename_is_not_a_new_lemma() -> None:
    """Duplicate detection compares the proposition, not the name."""
    from pcp.orch.sentinels import _body_of
    from pcp.orch.hashing import statement_hash

    a = statement_hash(_body_of("Lemma foo (P : iProp Σ) : P -∗ P."))
    b = statement_hash(_body_of("Lemma bar (P : iProp Σ) : P -∗ P."))
    assert a == b


def test_partial_correctness_is_flagged_but_does_not_block() -> None:
    from pcp.orch.sentinels import run_free_sentinels

    report = run_free_sentinels({"c": "Lemma c l v : l ↦ v -∗ WP !#l {{ w, ⌜w = v⌝ }}."})
    assert report.ok
    assert any("partial" in h.sentinel for h in report.hits)


def test_a_total_weakest_precondition_is_not_flagged() -> None:
    from pcp.orch.sentinels import run_free_sentinels

    report = run_free_sentinels({"c": "Lemma c l v : l ↦ v -∗ twp !#l {{ w, ⌜w = v⌝ }}."})
    assert not report.hits


def test_lateral_reductions_are_rejected_mechanically() -> None:
    """Restating your own goal is not progress -- the 'bridge proof' anti-pattern."""
    from pcp.orch.sentinels import reduction_sentinel

    hits = reduction_sentinel("Lemma goal (P Q : iProp Σ) : P -∗ Q.", "Lemma req (P Q : iProp Σ) : P -∗ Q.")
    assert hits and hits[0].blocking


def test_converging_failures_route_to_a_re_plan(graph: Graph) -> None:
    from pcp.orch.sentinels import converging_failures

    hits = converging_failures({"n7": "Lemma n7 (P : iProp Σ) : P -∗ False."},
                               "Lemma req (P : iProp Σ) : P -∗ False.")
    assert hits and hits[0].blocking and "re-plan" in hits[0].detail


# ------------------------------------------------------------------ amendments

def test_three_of_the_four_amendment_classes_are_auto_acceptable() -> None:
    from pcp.orch.amend import AUTO_ACCEPT, Amendment

    for klass in ("refute", "iso", "strengthen"):
        assert Amendment(node="n", klass=klass, statement="").auto_acceptable()
    assert not Amendment(node="n", klass="weaken", statement="").auto_acceptable()
    assert "weaken" not in AUTO_ACCEPT


def test_the_impact_report_is_computed_not_argued(graph: Graph) -> None:
    from pcp.orch.amend import impact_of

    _node(graph, "iface", rank="interface", name="iface")
    _node(graph, "client1", statement="Lemma client1 : iface -> True.")
    _node(graph, "client2", statement="Lemma client2 : True.")
    graph.add_edge("client1", "iface")
    graph.add_edge("client2", "iface")
    report = impact_of(graph, graph.get("iface"))
    # client1 mentions the amended name in its *statement*: statement-invalidation.
    assert report.statement_invalidated == ["client1"]
    assert report.reopened == ["client2"]
    assert "impact of amending" in report.render()


def test_audit_is_a_ladder_climbed_only_as_needed(graph: Graph) -> None:
    from pcp.orch.amend import Amendment, ImpactReport, audit_rung

    root = _node(graph, "root", rank="root")
    iface = _node(graph, "iface", rank="interface")
    local = _node(graph, "local", rank="local")
    weaken = Amendment(node="x", klass="weaken", statement="")
    small, big = ImpactReport(node="x"), ImpactReport(node="x", reopened=["a"] * 9)
    assert audit_rung(graph, root, weaken, big) == "human"
    assert audit_rung(graph, iface, weaken, small) == "one-auditor"
    assert audit_rung(graph, iface, weaken, big) == "quorum"
    assert audit_rung(graph, local, weaken, small) == "deterministic"
    iso = Amendment(node="x", klass="iso", statement="")
    assert audit_rung(graph, root, iso, big) == "deterministic"


def test_typeclass_plumbing_is_precleared() -> None:
    from pcp.orch.amend import precleared

    assert precleared(["inG Σ (authR natUR)", "Countable K"])
    assert not precleared(["Hn : n > 0"])
    assert not precleared([])


def test_refutation_taints_dependents_along_two_channels(graph: Graph) -> None:
    from pcp.orch.amend import taint

    bad = _node(graph, "bad", name="bad")
    _node(graph, "uses_it", statement="Lemma uses_it : True.", proof_status="gated", body="exact I.")
    _node(graph, "mentions_it", statement="Lemma mentions_it : bad -> True.", proof_status="gated", body="exact I.")
    graph.add_edge("uses_it", "bad")
    graph.add_edge("mentions_it", "bad")
    tainted = taint(graph, bad)
    assert set(tainted) == {"uses_it", "mentions_it"}
    # Proof-invalidation: statement stands, proof re-opens.
    assert graph.get("uses_it").proof_status == "open"
    assert graph.get("uses_it").statement_status == "frozen"
    # Statement-invalidation: the statement no longer means anything.
    assert graph.get("mentions_it").statement_status == "proposed"


# ---------------------------------------------------------------- decomposition

def test_a_plan_whose_glue_ignores_a_child_is_rejected(graph: Graph) -> None:
    from pcp.orch.decompose import DecompositionPolicy, Plan, accept_plan

    parent = _node(graph, "p")
    plan = Plan(parent="p", children=[("a", "..."), ("b", "...")], glue="iApply a.")
    ok, why = accept_plan(graph, parent, plan, DecompositionPolicy())
    assert not ok and "b" in why and "demands" in why


def test_the_depth_cap_forces_a_re_plan_rather_than_another_layer(graph: Graph) -> None:
    from pcp.orch.decompose import DecompositionPolicy, may_decompose

    deep = _node(graph, "deep", depth=2)
    ok, why = may_decompose(deep, DecompositionPolicy(depth_cap=2))
    assert not ok and "re-plan" in why


def test_strict_no_gap_is_opt_in(graph: Graph) -> None:
    from pcp.orch.decompose import DecompositionPolicy, Plan, accept_plan

    parent = _node(graph, "p")
    plan = Plan(parent="p", children=[("a", "...")], glue="iApply a.")
    assert accept_plan(graph, parent, plan, DecompositionPolicy())[0]
    strict = DecompositionPolicy(strict_no_gap=True)
    assert not accept_plan(graph, parent, plan, strict, glue_gated=False)[0]
    assert accept_plan(graph, parent, plan, strict, glue_gated=True)[0]


# --------------------------------------------------------------------- packets

def test_the_context_packet_is_deterministic_and_says_the_statement_is_frozen(
    graph: Graph, scratch_dir: Path, tmp_path: Path
) -> None:
    from pcp.orch.assemble import Development, NodeSpec
    from pcp.orch.packet import NODE_FILE, build_packet

    dev = Development(scratch_dir / "Basic.v")
    node = _node(graph, "child", name="child", statement="Lemma child (P : iProp Σ) : P -∗ P.",
                 intent="root goal: prove sep_comm\nwhy this node: it is the swap step")
    siblings = [NodeSpec("child", node.statement, body="admit.")]
    packet = build_packet(graph, node, dev, siblings, anchor="sep_comm", root=tmp_path)

    task = packet.task.read_text(encoding="utf-8")
    assert "frozen" in task
    assert "Never add a hypothesis" in task
    assert node.statement in task
    assert "it is the swap step" in task
    assert '"status": "contested"' in task
    meta = json.loads((packet.workdir / NODE_FILE).read_text(encoding="utf-8"))
    assert meta["target"] == "child" and meta["anchor"] == "sep_comm"
    assert (packet.workdir / "_CoqProject").exists()


def test_a_worker_answer_is_read_from_the_most_structured_channel(tmp_path: Path) -> None:
    from pcp.orch.runners.base import read_result

    (tmp_path / "answer.json").write_text(
        json.dumps({"status": "stuck", "evidence": "no idea",
                    "requests": [{"statement": "Lemma h : True.", "rationale": "would help"}]}),
        encoding="utf-8",
    )
    result = read_result(tmp_path, "ignored")
    assert result.status == "stuck" and result.requests[0].statement == "Lemma h : True."

    (tmp_path / "answer.json").unlink()
    (tmp_path / "proof.v").write_text("exact I.", encoding="utf-8")
    assert read_result(tmp_path, "").proof == "exact I."

    (tmp_path / "proof.v").unlink()
    assert read_result(tmp_path, "blah\n```coq\niFrame.\n```\n").proof == "iFrame."
    assert read_result(tmp_path, "nothing here").status == "stuck"


def test_proof_wrappers_are_tolerated() -> None:
    from pcp.orch.runners.base import strip_proof_wrapper

    assert strip_proof_wrapper("Proof.\n iFrame.\nQed.") == "iFrame."
    assert strip_proof_wrapper('Proof using Type. iFrame. Qed.') == "iFrame."
    assert strip_proof_wrapper("iFrame.") == "iFrame."


# --------------------------------------------------------------------- handoff

def test_handoff_puts_a_stuck_node_in_your_editor(graph: Graph) -> None:
    from pcp.orch.handoff import render_handoff

    _node(graph, "n", name="hard_lemma", statement="Lemma hard_lemma : True.",
                 proof_status="stuck", evidence="the spatial context was not empty at step 12")
    attempt = graph.start_attempt("n", runner="mock", owner="human")
    graph.finish_attempt(attempt, status="stuck", body="iIntros. wp_pures.",
                         requests=[{"statement": "Lemma helper : True.", "rationale": "unblocks it"}])
    text = render_handoff(graph, graph.get("n"))
    assert "Lemma hard_lemma : True." in text
    assert "iIntros. wp_pures." in text
    assert "spatial context was not empty" in text
    assert "Lemma helper : True." in text
    assert text.rstrip().endswith("Admitted.")


def test_an_unset_budget_is_not_an_exhausted_one() -> None:
    """Conflating the two silently blocks every decomposition."""
    assert Budget().unset and not Budget().exhausted()
    assert Budget(requests=0, tokens=0, dollars=0.0, seconds=1.0).exhausted() is True
    assert not Budget(requests=5).exhausted()


# --------------------------------------------------------------------- sandbox

def test_sandbox_argv_masks_the_answer_key_and_blackholes_the_forges(tmp_path: Path) -> None:
    from pcp.orch.runners.sandbox import Sandbox

    sb = Sandbox.for_benchmark(
        tmp_path / "work", repo=tmp_path / "repo", reference=tmp_path / "ref", network=True
    )
    argv = sb.wrap(["true"])
    joined = " ".join(argv)
    assert "--tmpfs" in joined and str(Path.home()) in joined, "home must be replaced"
    # The answer key is masked even though the repo is bound.
    assert argv.count("--tmpfs") >= 2
    hosts = [a for a in argv if "pcp-sandbox/hosts-" in a]
    assert hosts, "a blackhole hosts file must be bound when the network is up"
    text = Path(hosts[0]).read_text(encoding="utf-8")
    for host in ("github.com", "gitlab.mpi-sws.org"):
        assert f"127.0.0.1 {host}" in text
    # Documentation sites are deliberately left alone.
    assert "127.0.0.1 iris-project.org" not in text


def test_sandbox_without_network_needs_no_hosts_file(tmp_path: Path) -> None:
    from pcp.orch.runners.sandbox import Sandbox

    sb = Sandbox.for_benchmark(tmp_path / "w", repo=tmp_path / "r", network=False)
    argv = sb.wrap(["true"])
    assert "--unshare-net" in argv
    assert not [a for a in argv if "pcp-sandbox/hosts-" in a]


def test_the_hosts_file_is_shared_not_per_attempt(tmp_path: Path) -> None:
    """A fresh temp file per attempt races with /tmp cleanup, and the failure looks
    like a worker error rather than a sandbox one."""
    from pcp.orch.runners.sandbox import Sandbox

    a = Sandbox.for_benchmark(tmp_path / "a", repo=tmp_path / "r", network=True).wrap(["true"])
    b = Sandbox.for_benchmark(tmp_path / "b", repo=tmp_path / "r", network=True).wrap(["true"])
    ha = [x for x in a if "pcp-sandbox/hosts-" in x][0]
    hb = [x for x in b if "pcp-sandbox/hosts-" in x][0]
    assert ha == hb and Path(ha).exists()


async def test_sandboxed_runner_does_not_mutate_the_wrapped_runner(tmp_path: Path) -> None:
    """The whole frontier dispatches at once; swapping a shared argv races."""
    from pcp.orch.runners.base import NodePayload
    from pcp.orch.runners.cli import claude_headless_runner
    from pcp.orch.runners.sandbox import Sandbox, SandboxedRunner, available

    if not available():
        pytest.skip("bubblewrap not installed")
    inner = claude_headless_runner()
    before = list(inner.argv)
    runner = SandboxedRunner(
        inner=inner,
        sandbox_factory=lambda w: Sandbox.for_benchmark(w, repo=tmp_path, network=False),
    )
    workdir = tmp_path / "w"
    workdir.mkdir()
    (workdir / "TASK.md").write_text("noop", encoding="utf-8")
    await runner.run_node(
        NodePayload(node_id="n", name="n", statement="", file="", workdir=workdir, budget_seconds=5)
    )
    assert inner.argv == before, "the wrapped runner's argv must be untouched"


def test_the_packet_carries_local_documentation_and_the_design_brief(
    graph: Graph, scratch_dir: Path, tmp_path: Path
) -> None:
    """Both were silently dropped on the eval path: `docs=None` meant "none" rather
    than "whatever is on this machine", and the brief landed after the answer
    instructions instead of next to the statement."""
    from pcp.orch.assemble import Development
    from pcp.orch.packet import render_task

    dev = Development(scratch_dir / "Basic.v")
    node = _node(graph, "n", name="sep_comm", statement="Lemma sep_comm : True.")
    text = render_task(
        node, dev, [], scratch_name="Basic.v",
        design="# Design brief\n\nThe invariant is given.",
        docs=[("everything in Iris", "/somewhere/index.txt")],
    )
    assert "## Documentation" in text
    assert "/somewhere/index.txt" in text
    assert "The invariant is given." in text
    # Context before instructions.
    assert text.index("Design brief") < text.index("## How to answer")


def test_docs_can_be_explicitly_empty(graph: Graph, scratch_dir: Path) -> None:
    from pcp.orch.assemble import Development
    from pcp.orch.packet import render_task

    dev = Development(scratch_dir / "Basic.v")
    node = _node(graph, "n2", name="sep_comm", statement="Lemma sep_comm : True.")
    assert "## Documentation" not in render_task(node, dev, [], scratch_name="Basic.v", docs=[])


# ------------------------------------------------- partial recovery on a deadline

def test_a_killed_worker_s_edited_file_is_recovered(tmp_path: Path) -> None:
    """PLAN.md 6: a kill is followed by a requeue "with the partial trace as
    evidence" -- which is worth nothing if the partial is dropped.

    The packet tells the worker to edit the assembled `.v` in place, so that is
    where a worker killed at its deadline has usually written its proof, and
    nowhere else.  A real run lost 91 lines of work on the hardest lemma this way.
    """
    from pcp.orch.runners.base import read_edited_body, read_result

    work = tmp_path / "w"
    work.mkdir()
    (work / "pcp-node.json").write_text(json.dumps({"target": "hard_spec"}), encoding="utf-8")
    (work / "Dev.v").write_text(
        "Lemma hard_spec : True.\nProof.\n  iIntros \"H\".\n  wp_pures.\nQed.\n", encoding="utf-8"
    )
    body = read_edited_body(work)
    assert body.splitlines()[0].strip() == 'iIntros "H".'
    assert "wp_pures." in body

    # And the general reader picks it up as a *partial*, not a claimed success.
    result = read_result(work, "")
    assert result.status == "stuck"
    assert "wp_pures." in result.proof
    assert "recovered a partial proof" in result.evidence


def test_an_untouched_placeholder_is_not_reported_as_progress(tmp_path: Path) -> None:
    """A worker that did nothing must not look like one that got close."""
    from pcp.orch.runners.base import read_edited_body, read_result

    work = tmp_path / "w"
    work.mkdir()
    (work / "pcp-node.json").write_text(json.dumps({"target": "t"}), encoding="utf-8")
    (work / "Dev.v").write_text("Lemma t : True.\nProof.\nadmit.\nAdmitted.\n", encoding="utf-8")
    assert read_edited_body(work) == ""
    assert "no answer.json" in read_result(work, "").evidence


def test_recovery_is_skipped_without_node_metadata(tmp_path: Path) -> None:
    from pcp.orch.runners.base import read_edited_body

    work = tmp_path / "w"
    work.mkdir()
    (work / "Dev.v").write_text("Lemma t : True.\nProof. exact I. Qed.\n", encoding="utf-8")
    assert read_edited_body(work) == ""


# ------------------------------------------- the orchestrator does no proof work

def test_a_decomposer_cannot_attach_a_proof_at_any_level(graph: Graph) -> None:
    """Three independent barriers, because one of them is a prompt and prompts leak.

    This is the store-level one: whatever a decomposer returns, the graph refuses to
    write it as a proof.
    """
    from pcp.orch.graph import RoleViolation

    _node(graph, "n")
    for role in ("decomposer", "auditor", "human", "gate"):
        with pytest.raises(RoleViolation):
            graph.set_proof_status("n", "gated", body="exact I.", role=role)
    # Even the raw update path is closed.
    with pytest.raises(RoleViolation):
        graph.update("n", body="exact I.")
    # And the one legitimate route works.
    graph.record_proof("n", "exact I.")
    assert graph.get("n").body == "exact I."


def test_a_proposal_carrying_proof_text_is_rejected() -> None:
    """The type-level barrier: a proposal has nowhere to put a proof, and every
    statement is screened before it can become a node."""
    from pcp.orch.decompose import ProofEngineeringAttempt, parse_proposal

    for payload, why in (
        ('{"children":[{"name":"h","statement":"Lemma h : True. Proof. exact I. Qed."}]}', "proof block"),
        ('{"children":[{"name":"h","statement":"Lemma h : True.\\nProof.\\nAdmitted."}]}', "admitted"),
        ('{"children":[{"name":"h","statement":"iIntros \\"H\\". iFrame."}]}', "bare tactics"),
        ('{"children":[{"name":"h","statement":"Lemma h : True. wp_pures."}]}', "trailing tactic"),
    ):
        with pytest.raises(ProofEngineeringAttempt, match="does not prove"):
            parse_proposal(payload)


def test_a_valid_proposal_is_accepted_and_carries_no_body() -> None:
    from dataclasses import fields

    from pcp.orch.decompose import PlanProposal, parse_proposal, validate_proposal

    proposal = parse_proposal(
        '{"rationale":"split the write","children":['
        '{"name":"swap_half","statement":"Lemma swap_half (P Q : iProp Σ) : P ∗ Q -∗ Q ∗ P."}]}'
    )
    assert validate_proposal(proposal) == []
    assert proposal.names() == ["swap_half"]
    # There is no field a proof could travel in -- that is the enforcement.
    names = {f.name for f in fields(PlanProposal)}
    assert not (names & {"body", "proof", "script", "tactics"})


def test_an_empty_plan_is_a_failure_because_orchestration_is_required() -> None:
    from pcp.orch.decompose import parse_proposal, validate_proposal

    problems = validate_proposal(parse_proposal('{"children":[]}'))
    assert problems and "orchestration is required" in problems[0]


def test_children_must_be_lemmas_named_as_declared() -> None:
    from pcp.orch.decompose import parse_proposal, validate_proposal

    mismatched = parse_proposal('{"children":[{"name":"a","statement":"Lemma b : True."}]}')
    assert any("exactly one declaration named a" in p for p in validate_proposal(mismatched))
    notalemma = parse_proposal('{"children":[{"name":"d","statement":"Definition d := 0."}]}')
    assert any("children must be lemmas" in p for p in validate_proposal(notalemma))


def test_the_decomposer_runner_has_no_way_to_write_or_execute() -> None:
    """The capability barrier. It cannot run coqc, so it cannot iterate on a proof."""
    from pcp.orch.decomposer import DECOMPOSER_TOOLS, decomposer_runner

    argv = decomposer_runner().argv
    assert "Read" in argv and "Grep" in argv
    for banned in ("Write", "Edit", "Bash", "NotebookEdit"):
        assert banned not in argv, f"the decomposer must not be granted {banned}"
    assert set(DECOMPOSER_TOOLS.split(",")) == {"Read", "Glob", "Grep"}


def test_the_decomposer_packet_never_offers_a_way_to_check_a_proof(
    graph: Graph, scratch_dir: Path
) -> None:
    from pcp.orch.assemble import Development
    from pcp.orch.decomposer import render_decomposition_task

    dev = Development(scratch_dir / "Basic.v")
    node = _node(graph, "r", name="sep_comm", statement="Lemma sep_comm : True.")
    task = render_decomposition_task(node, dev)
    assert "decomposer" in task.lower()
    assert "pcp check" not in task
    assert "you are not proving" in task.lower()
    assert '"children"' in task

    # The answer template must stay a *template*. Its worked example once read
    #   {"name": "value", "text": "Definition value (γ : gname) (n : Z) := ghost_var γ (1/2) n."}
    # which names one of the rwcas rung's blank predicates and gives it a
    # defensible body -- half-ownership ghost_var is the standard idiom for the
    # client half of a linearizable cell. That is the single hardest design
    # decision on the rung, handed over in the prompt that asks for it. An example
    # has to show the shape without choosing anyone's ghost state.
    for leak in ("ghost_var", "iris.base_logic.lib", "(1/2)"):
        assert leak not in task, f"the answer template leaks a design choice: {leak}"


def test_a_decomposer_reports_the_runner_s_reason_not_a_parse_failure(
    graph: Graph, scratch_dir
) -> None:
    """A killed runner has already said why, and that outranks the silence after it.

    Parsing the empty output regardless recorded a decomposer killed at its deadline
    as `the decomposer produced no JSON object to read` -- which reads as the model
    ignoring the protocol, and sends you to rewrite the prompt when the fix is a
    bigger budget.
    """
    import asyncio
    from dataclasses import dataclass

    from pcp.orch.assemble import Development
    from pcp.orch.decomposer import Decomposer
    from pcp.orch.runners.base import NodeResult

    @dataclass
    class Killed:
        name: str = "cli"

        def available(self) -> bool:
            return True

        async def run_node(self, node):
            return NodeResult(
                status="stuck",
                evidence="worker exceeded its 900s deadline and was killed",
            )

    dev = Development(scratch_dir / "Basic.v")
    node = _node(graph, "r", name="sep_comm", statement="Lemma sep_comm : True.")
    d = Decomposer(graph, dev, Killed(), workroot=scratch_dir / "w")
    out = asyncio.run(d.propose(node, budget_seconds=1))

    assert not out.ok
    assert "deadline" in out.violation
    assert "JSON" not in out.violation


def test_an_attempt_records_who_ran_it_separately_from_who_stated_it(graph: Graph) -> None:
    """`owner` is provenance; `runner` and `role` are who did the work.

    They were conflated under the name `tier`, so a prover attempt on a child the
    decomposer had proposed was emitted as `tier: decomposer` -- which reads as the
    decomposer having run it. Nothing consumed the field, so nothing corrected it,
    and model attribution is the one question the records exist to answer.
    """
    _node(graph, "n", owner="decomposer")
    graph.start_attempt("n", runner="sandboxed:claude:claude-sonnet-5/medium",
                        owner="decomposer", role="prover")
    started = [e for e in graph.events_since() if e["kind"] == "attempt.started"][-1]
    assert started["payload"]["owner"] == "decomposer"
    assert started["payload"]["role"] == "prover"
    assert "sonnet" in started["payload"]["runner"]
    assert "tier" not in started["payload"]


def test_a_packet_names_the_tools_it_granted(graph: Graph, scratch_dir) -> None:
    """A granted tool the worker is never told about is an ungranted tool.

    `describe_tools` was written with that warning in its own docstring and then had
    no callers, so an ablation that granted ten state tools described none of them.
    Five of seven workers never touched them, and the two that did had spent a turn
    on tool discovery first. The control arm has to stay quiet, though: telling a
    worker about tools it does not have is how the *other* arm loses turns.
    """
    from pcp.orch.assemble import Development
    from pcp.orch.packet import build_packet

    dev = Development(scratch_dir / "Basic.v")
    node = _node(graph, "n", name="sep_comm", statement="Lemma sep_comm : True.")

    off = build_packet(graph, node, dev, [], anchor="sep_comm", root=scratch_dir / "off")
    text = (off.workdir / "TASK.md").read_text()
    assert "Tools available to you" not in text
    assert "mcp__pcp__" not in text

    on = build_packet(graph, node, dev, [], anchor="sep_comm", root=scratch_dir / "on",
                      state_tools=["proof_open", "premise_search"])
    text = (on.workdir / "TASK.md").read_text()
    assert "## Tools available to you" in text
    assert "mcp__pcp__proof_open" in text
    assert "mcp__pcp__premise_search" in text
    # only what was granted
    assert "mcp__pcp__proof_try" not in text


def test_a_parallel_childs_deadline_is_not_divided_among_its_siblings() -> None:
    """Children are gathered concurrently, so wall-clock is not a shared pool.

    seqlock_wf: a 7200 s root split six ways gave every child 1200 s. Four used
    78/479/522/983 s; the two hardest were killed at the deadline with 2738 s of
    their siblings' allowance unspent -- and they were the run's only failures.
    """
    from pcp.orch.graph import Budget

    parent = Budget(requests=60, tokens=6000, dollars=6.0, seconds=7200)
    child = parent.split(6)

    assert child.seconds == 7200, "a concurrent child must keep the full deadline"
    # The metered dimensions are a shared pool and must still divide.
    assert child.requests == 10
    assert child.tokens == 1000
    assert child.dollars == 1.0


def test_share_still_scales_the_clock() -> None:
    """`share` means "use this fraction of the parent's time" -- a real instruction."""
    from pcp.orch.graph import Budget

    probe = Budget(seconds=1000).split(1, share=0.25)
    assert probe.seconds == 250
