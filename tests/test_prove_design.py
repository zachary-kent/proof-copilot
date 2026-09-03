

# --- where a new declaration goes ---------------------------------------------

_FILE = """From iris.heap_lang Require Import lang proofmode notation.

Class rwcasG Σ := {
  rwcas_heapGS :: heapGS Σ;
  rwcas_reg :: inG Σ regUR;
}.

Section rwcas.
  Context `{!rwcasG Σ}.

  Definition value (γ : gname) (n : Z) : iProp Σ := marker γ n.

  Lemma spec : True.
  Proof.
  Admitted.
End rwcas.
"""


def test_an_addition_lands_before_its_first_use() -> None:
    """A resource algebra used by the typeclass must precede the typeclass.

    Anchoring every addition at the first obligation put it below the definitions
    that used it, so the design did not compile and the decomposer was asked to
    revise a design that was never wrong.
    """
    from pcp.orch.prove import _place_additions

    out = _place_additions(
        _FILE,
        [
            "Definition regUR : ucmra := authUR (gmapUR nat unitR).",
            "Definition marker (γ : gname) (n : Z) : iProp Σ := own γ (to_agree n).",
        ],
    )
    assert out.index("Definition regUR") < out.index("Class rwcasG")
    # ... and one used inside the Section must stay inside it, for `Σ`.
    assert out.index("Section rwcas.") < out.index("Definition marker")
    assert out.index("Definition marker") < out.index("Definition value")


def test_an_addition_nothing_uses_falls_back_to_the_first_obligation() -> None:
    from pcp.orch.prove import _place_additions

    out = _place_additions(_FILE, ["Definition orphan : nat := 0."])
    assert out.index("Definition value") < out.index("Definition orphan")
    assert out.index("Definition orphan") < out.index("Lemma spec")


def test_additions_are_ordered_against_each_other() -> None:
    """An addition used only by another addition must still precede it.

    This killed a real run. The decomposer's design for `rwcas` was sound -- a
    ghost_map registry of write slots, each holding either a pending atomic update
    or a saved-prop completion token -- and it listed the definitions in correct
    dependency order: `write_au`, `write_done`, then the `write_slot` that uses
    both. Assembly reordered them into a broken one. `write_slot` matched the
    freshly-substituted `rwcas_inv` and moved up; its two dependencies were named
    nowhere in the *original* file, so they matched nothing, fell back to the first
    proof block, and landed below their own consumer. Three design rounds all died
    on `The reference write_au was not found in the current environment`, and the
    decomposer was asked three times to revise a design that was never wrong.
    """
    from pcp.orch.prove import _place_additions

    text = _FILE.replace(
        "  Definition value (γ : gname) (n : Z) : iProp Σ := marker γ n.",
        "  Definition value (γ : gname) (n : Z) : iProp Σ := slot γ n.",
    )
    out = _place_additions(
        text,
        [
            "Definition au (γ : gname) : iProp Σ := True.",
            "Definition done (i : gname) : iProp Σ := True.",
            "Definition slot (γ : gname) (n : Z) : iProp Σ := au γ ∨ done γ.",
        ],
    )
    assert out.index("Definition au") < out.index("Definition slot")
    assert out.index("Definition done") < out.index("Definition slot")
    assert out.index("Definition slot") < out.index("Definition value")


def test_a_dependency_chain_among_additions_is_ordered_throughout() -> None:
    """The pull propagates down a chain, so it is iterated to a fixpoint.

    Listed deepest-first to make sure the result comes from the dependencies and
    not from the order the decomposer happened to choose.
    """
    from pcp.orch.prove import _place_additions

    out = _place_additions(
        _FILE,
        [
            "Definition c (γ : gname) : iProp Σ := b γ.",
            "Definition b (γ : gname) : iProp Σ := a γ.",
            "Definition a (γ : gname) : iProp Σ := marker γ 0.",
            "Definition marker (γ : gname) (n : Z) : iProp Σ := own γ (to_agree n).",
        ],
    )
    for earlier, later in (("marker", "a"), ("a", "b"), ("b", "c")):
        assert out.index(f"Definition {earlier}") < out.index(f"Definition {later}"), out


def test_a_cycle_among_additions_does_not_hang() -> None:
    """Not expressible in Coq, so it fails at the compile either way -- but the
    placement must terminate and hand the decomposer that error, not spin."""
    from pcp.orch.prove import _place_additions

    out = _place_additions(
        _FILE,
        [
            "Definition p (γ : gname) : iProp Σ := q γ.",
            "Definition q (γ : gname) : iProp Σ := p γ.",
        ],
    )
    assert "Definition p" in out and "Definition q" in out


# --- what a design revision does to obligations it no longer wants ---------------

def _plan(*names):
    from pcp.orch.decompose import ChildStatement, PlanProposal

    return PlanProposal(
        children=tuple(ChildStatement(name=n, statement=f"Lemma {n} : True.") for n in names)
    )


def _rooted(tmp_path):
    from pcp.orch.graph import Graph, Node
    from pcp.orch.prove import ProveConfig

    graph = Graph(tmp_path / "g.db")
    root = graph.add_node(
        Node(id="r", name="r", statement="Lemma r : True.", rank="root", parent=None)
    )
    return graph, root, ProveConfig(file=tmp_path / "X.v", target="r")


def _live(graph):
    return sorted(
        n.name for n in graph.nodes()
        if n.rank != "root" and n.proof_status != "attic" and not n.body
    )


def test_a_revision_retires_the_obligations_it_drops(tmp_path) -> None:
    """`attic` was a status the schema defined and no code ever wrote.

    So an amendment that changed the split orphaned what it dropped: the node stayed
    `open`, the frontier kept dispatching workers at a lemma no design asked for --
    against definitions the revision may have deleted -- and `integrate()` demands a
    body from every non-attic node, so the run could never finish. It had not bitten
    only because no run had yet completed a design amendment.
    """
    from pcp.orch.prove import _adopt_proposal

    graph, root, cfg = _rooted(tmp_path)
    _adopt_proposal(cfg, graph, root, _plan("helper_a", "keep_me"))
    assert _live(graph) == ["helper_a", "keep_me"]

    _adopt_proposal(cfg, graph, root, _plan("helper_b", "keep_me"))
    assert _live(graph) == ["helper_b", "keep_me"], "the dropped obligation still blocks"
    assert graph.by_name("helper_a").proof_status == "attic"


def test_a_revision_revives_an_obligation_it_asks_for_again(tmp_path) -> None:
    """The name is taken, so without this the design asks for a lemma that stays in
    the attic -- never dispatched, and waited on forever by integration."""
    from pcp.orch.prove import _adopt_proposal

    graph, root, cfg = _rooted(tmp_path)
    _adopt_proposal(cfg, graph, root, _plan("helper_a"))
    _adopt_proposal(cfg, graph, root, _plan("helper_b"))
    assert graph.by_name("helper_a").proof_status == "attic"

    _adopt_proposal(cfg, graph, root, _plan("helper_a"))
    assert graph.by_name("helper_a").proof_status == "open"
    assert graph.by_name("helper_b").proof_status == "attic"
    assert _live(graph) == ["helper_a"]


def test_a_proved_obligation_is_not_retired_when_dropped(tmp_path) -> None:
    """The root's proof may still cite it, and retiring it would break the assembly.

    `_revalidate` is the right owner for the stale case: it re-opens any proof the
    new definitions invalidated, which turns a stale proved orphan into an unproved
    one that the next round retires.
    """
    from pcp.orch.prove import _adopt_proposal

    graph, root, cfg = _rooted(tmp_path)
    _adopt_proposal(cfg, graph, root, _plan("proved_one", "unproved_one"))
    graph.record_proof("proved_one", "Proof. exact I. Qed.")

    _adopt_proposal(cfg, graph, root, _plan("something_else"))
    assert graph.by_name("proved_one").proof_status != "attic"
    assert graph.by_name("unproved_one").proof_status == "attic"


def test_retirement_is_visible_in_the_trace(tmp_path) -> None:
    from pcp.orch.prove import _adopt_proposal

    graph, root, cfg = _rooted(tmp_path)
    _adopt_proposal(cfg, graph, root, _plan("helper_a"))
    _adopt_proposal(cfg, graph, root, _plan("helper_b"))
    kinds = {e["kind"]: e["payload"] for e in graph.events_since()}
    assert kinds["plan.retired"]["retired"] == ["helper_a"]
    assert kinds["plan.adopted"]["retired"] == ["helper_a"]


def test_a_contract_violation_is_revisable_rather_than_fatal() -> None:
    """The commonest failure on a rung whose design is given must reach the loop.

    `_apply_with_revision`'s own docstring records this lesson for compile errors:
    aborting there "made the commonest case the one case the revision loop could not
    reach". The contract check sat one line away and still aborted, and it cost a
    whole rwcas rung.
    """
    import inspect

    from pcp.orch import prove

    source = inspect.getsource(prove._apply_design)
    assert "DesignViolatesContract" in source
    assert "OrchestrationRequired" not in source.split("contract.check")[1]

    for fn in (prove._apply_with_revision, prove.prove):
        body = inspect.getsource(fn)
        if "DesignDoesNotCompile" in body:
            assert "DesignViolatesContract" in body, (
                f"{fn.__name__} retries a design that does not compile but not one "
                "the contract refused; both are mistakes the decomposer can correct"
            )


def test_the_decomposer_is_told_when_the_design_is_already_given(tmp_path) -> None:
    """Saying nothing read as permission, and the decomposer rewrote the invariant."""
    from pcp.orch.assemble import Development
    from pcp.orch.decomposer import render_decomposition_task
    from pcp.orch.graph import Node

    src = tmp_path / "Dev.v"
    src.write_text(
        "Definition inv (x : nat) : Prop := x = x.\n"
        "Lemma a : True.\nProof.\nAdmitted.\n", encoding="utf-8")
    node = Node(id="a", name="a", statement="Lemma a : True.", parent=None)
    text = render_decomposition_task(node, Development(src))

    assert "The design is already there" in text
    assert "frozen" in text
    assert "designing it is your job" not in text


def test_a_blank_design_still_asks_for_one(tmp_path) -> None:
    from pcp.orch.assemble import Development
    from pcp.orch.decomposer import render_decomposition_task
    from pcp.orch.graph import Node

    src = tmp_path / "Dev.v"
    src.write_text(
        "Definition value (x : nat) : Prop := True.\n"
        "Lemma a : True.\nProof.\nAdmitted.\n", encoding="utf-8")
    node = Node(id="a", name="a", statement="Lemma a : True.", parent=None)
    text = render_decomposition_task(node, Development(src))

    assert "designing it is your job" in text
    assert "The design is already there" not in text


def test_an_amendment_on_a_given_design_asks_for_obligations_not_definitions(tmp_path) -> None:
    """Otherwise a round of an expensive model produces what the contract refuses."""
    from pcp.orch.assemble import Development
    from pcp.orch.decomposer import render_amendment_task
    from pcp.orch.graph import Node

    src = tmp_path / "Dev.v"
    src.write_text("Definition inv (x : nat) : Prop := x = x.\n"
                   "Lemma a : True.\nProof.\nAdmitted.\n", encoding="utf-8")
    node = Node(id="a", name="a", statement="Lemma a : True.", parent=None)
    text = render_amendment_task(node, Development(src), design=[], evidence="it failed", round_no=2)

    assert "given and frozen" in text
    assert "the revised design, complete" not in text


def test_a_child_given_as_a_bare_proposition_gets_its_header() -> None:
    """The decomposer reads "statement" as the proposition, and it is not wrong to.

    A real rwcas revision proposed three sound obligations this way, was rejected for
    "must be exactly one declaration", and the run lost the repair that would have
    integrated it. The name is supplied separately, so the header is derivable.
    """
    from pcp.orch.decompose import parse_proposal, validate_proposal

    proposal = parse_proposal('{"children": [{"name": "collect_later", "statement": '
                              '"\\u2200 (P : Prop), P -> P"}]}')
    child = proposal.children[0]
    assert child.statement.startswith("Lemma collect_later :")
    assert child.statement.rstrip().endswith(".")
    assert validate_proposal(proposal) == []


def test_a_child_that_already_declares_itself_is_left_alone() -> None:
    from pcp.orch.decompose import parse_proposal

    text = "Lemma already (n : nat) : n = n."
    proposal = parse_proposal('{"children": [{"name": "already", "statement": %s}]}'
                              % __import__("json").dumps(text))
    assert proposal.children[0].statement == text


def test_a_child_declared_under_another_name_is_still_refused() -> None:
    """Filling in a missing header must never become renaming someone's lemma."""
    from pcp.orch.decompose import parse_proposal, validate_proposal

    proposal = parse_proposal('{"children": [{"name": "wanted", "statement": '
                              '"Lemma something_else (n : nat) : n = n."}]}')
    assert any("wanted" in p for p in validate_proposal(proposal))


def test_a_child_statement_that_does_not_typecheck_is_caught_before_dispatch(tmp_path) -> None:
    """A frozen statement is inserted into every sibling's file, so one bad one
    poisons all of them.

    `_apply_design` already compiled the *definitions* for exactly this reason --
    "a design that does not compile poisons every node beneath it" -- but children
    are inserted by `assemble` at gate time and were never elaborated. A seqlock_wf
    round proposed `z = 1 + Z.of_nat ver` (no `%Z`, so `nat_scope` rejects it) and 14
    workers were dispatched against a file that could never compile.
    """
    import inspect

    from pcp.orch import prove

    source = inspect.getsource(prove._apply_design)
    head, _, tail = source.partition("_compile(Assembly(text=patched))")
    assert tail, "the design compile guard moved; re-check this test"
    assert "proposal.children" in tail, (
        "child statements are frozen and inserted into every worker's file, so they "
        "must be elaborated before dispatch, not only the design's definitions"
    )
    assert "stub_prefix=True" in tail, "the check must use the fast per-node shape"


def test_the_offending_child_is_named_when_the_compiler_identifies_it() -> None:
    from pcp.orch.assemble import NodeSpec
    from pcp.orch.prove import _blame_child

    specs = [NodeSpec(name="fc50_acquire", statement="", body=None),
             NodeSpec(name="fc50_release", statement="", body=None)]
    detail = 'File "./M.v", line 376: Error: in fc50_acquire the term has type Z'
    assert _blame_child(detail, specs) == " (`fc50_acquire`)"
    # Ambiguous or silent compiler output blames nobody rather than guessing.
    assert _blame_child("Error: something", specs) == ""
    assert _blame_child("fc50_acquire and fc50_release", specs) == ""


def test_a_decomposition_killed_by_the_clock_is_retried_with_more_of_it() -> None:
    """A deadline is not a judgement -- nothing was proposed, so nothing was wrong.

    `cached_strong` is 3180 lines; its first design round was killed at 1800 s and
    that ended the run, while a design that merely failed to *compile* would have had
    three revisions. Same mistake as the contract check: a recoverable failure on a
    path with no recovery.
    """
    import asyncio

    from pcp.orch import prove

    budgets: list[float] = []

    class _Decomposer:
        def __init__(self, *a, **k) -> None: ...

        async def propose(self, root, *, contract, budget_seconds):
            budgets.append(budget_seconds)
            return type("R", (), {"ok": False, "infrastructure": False,
                                  "violation": "worker exceeded its 1800s deadline and was killed"})()

    class _Cfg:
        decomposer_runner = object(); workroot = "/tmp"; corpus = ""; library = ()
        decomposer_seconds = 100.0; contract = None; results = (); file = "X.v"

    import pcp.orch.decomposer as dm
    original = dm.Decomposer
    try:
        dm.Decomposer = _Decomposer
        graph = type("G", (), {"emit": lambda *a, **k: None})()
        asyncio.run(prove._decompose(_Cfg(), graph, _FakeDev(), _FakeNode()))
    finally:
        dm.Decomposer = original

    assert budgets == [100.0, 200.0, 400.0], f"expected doubling retries, got {budgets}"


def test_an_infrastructure_failure_is_not_retried_with_a_longer_clock() -> None:
    """A revoked credential does not get better with more time."""
    import asyncio

    from pcp.orch import prove

    calls = []

    class _Decomposer:
        def __init__(self, *a, **k) -> None: ...

        async def propose(self, root, *, contract, budget_seconds):
            calls.append(budget_seconds)
            return type("R", (), {"ok": False, "infrastructure": True,
                                  "violation": "401 access token has been revoked"})()

    class _Cfg:
        decomposer_runner = object(); workroot = "/tmp"; corpus = ""; library = ()
        decomposer_seconds = 100.0; contract = None; results = (); file = "X.v"

    import pcp.orch.decomposer as dm
    original = dm.Decomposer
    try:
        dm.Decomposer = _Decomposer
        graph = type("G", (), {"emit": lambda *a, **k: None})()
        asyncio.run(prove._decompose(_Cfg(), graph, _FakeDev(), _FakeNode()))
    finally:
        dm.Decomposer = original

    assert calls == [100.0], "an outage must not be retried"


class _FakeDev:
    source = ""
    path = __import__("pathlib").Path("X.v")


class _FakeNode:
    id = "n"
    name = "n"
    budget = type("B", (), {"seconds": 10800.0})()


def test_a_deadline_retry_never_exceeds_the_runs_own_budget() -> None:
    """Doubling a generous clock can outlive the wall it runs inside.

    4500 s on the cached rungs doubles to 9000 s within a 10800 s budget: the retry
    would be killed by the outer timeout, wasting both rounds instead of one.
    """
    import asyncio

    from pcp.orch import prove

    budgets: list[float] = []

    class _Decomposer:
        def __init__(self, *a, **k) -> None: ...

        async def propose(self, root, *, contract, budget_seconds):
            budgets.append(budget_seconds)
            return type("R", (), {"ok": False, "infrastructure": False,
                                  "violation": "worker exceeded its 4500s deadline and was killed"})()

    class _Cfg:
        decomposer_runner = object(); workroot = "/tmp"; corpus = ""; library = ()
        decomposer_seconds = 4500.0; contract = None; results = (); file = "X.v"

    class _Node:
        id = "n"; name = "n"
        budget = type("B", (), {"seconds": 10800.0})()

    import pcp.orch.decomposer as dm
    original = dm.Decomposer
    try:
        dm.Decomposer = _Decomposer
        graph = type("G", (), {"emit": lambda *a, **k: None})()
        asyncio.run(prove._decompose(_Cfg(), graph, _FakeDev(), _Node()))
    finally:
        dm.Decomposer = original

    assert sum(budgets) <= 10800.0, f"planned {sum(budgets)}s inside a 10800s budget: {budgets}"
    assert budgets[0] == 4500.0


def test_a_child_that_already_exists_in_the_development_is_rejected(tmp_path) -> None:
    """Naming an existing lemma as an obligation is the opposite of using it.

    One rwcas round proposed `cd19`, `f17_update` and `bfd18_agree` -- all three
    already declared and Qed'd in the file. The harness froze a second declaration
    under each name and dispatched workers to re-prove them; the one sent after
    `cd19` spent two attempts discovering its lemma was proved forty lines above the
    anchor.
    """
    from pcp.orch.assemble import Development
    from pcp.orch.decompose import ChildStatement
    from pcp.orch.decomposer import _already_proved

    src = tmp_path / "Dev.v"
    src.write_text("Lemma cd19 (n : nat) : n = n.\nProof. done. Qed.\n"
                   "Lemma target : True.\nProof.\nAdmitted.\n", encoding="utf-8")

    class _P:
        children = (ChildStatement(name="cd19", statement="Lemma cd19 (n:nat) : n = n."),
                    ChildStatement(name="genuinely_new", statement="Lemma genuinely_new : True."))

    problems = _already_proved(Development(src), _P())
    assert len(problems) == 1
    assert "cd19" in problems[0] and "use it" in problems[0]


def test_worker_lemma_requests_reach_the_decomposer() -> None:
    """The packet promises requests "go back to whoever stated this node".

    Nothing kept that promise: `schedule.py` recorded them, `prove.py` never read
    them, and the amendment prompt never mentioned them. That made the one channel a
    worker has for saying *this obligation is too large, split it here* a dead end --
    on cached_strong, `c129_register` requested exactly the bridging lemma it was
    blocked on and the request went nowhere.
    """
    from pcp.orch.prove import _design_evidence
    from pcp.orch.schedule import NodeOutcome, RunReport

    report = RunReport()
    report.outcomes = [
        NodeOutcome(node_id="1", name="c129_register", status="stuck",
                    evidence="could not bridge backup",
                    requests=[{"statement": "Lemma f111_spec_same_backup : True.",
                               "rationale": "pins backup across the re-existentialisation"}]),
        NodeOutcome(node_id="2", name="fine", status="qed", evidence=""),
    ]
    text = _design_evidence(report)

    assert "f111_spec_same_backup" in text
    assert "pins backup" in text
    assert "asked to exist" in text
    # A request is evidence for the decomposer to judge, never an adopted obligation.
    assert "requests, not decisions" in text


def test_a_run_with_no_requests_says_nothing_about_them() -> None:
    from pcp.orch.prove import _design_evidence
    from pcp.orch.schedule import NodeOutcome, RunReport

    report = RunReport()
    report.outcomes = [NodeOutcome(node_id="1", name="a", status="stuck", evidence="boom")]
    assert "asked to exist" not in _design_evidence(report)


def test_the_decomposer_is_told_to_prefer_smaller_obligations(tmp_path) -> None:
    """Child count was flat (4-9) while target size varied 9x, so per-obligation
    difficulty swung 20x and the solve rate tracked it: 13 tactics/child -> 8/9
    proved; 267 tactics/child -> 2/4."""
    from pcp.orch.assemble import Development
    from pcp.orch.decomposer import render_decomposition_task
    from pcp.orch.graph import Node

    src = tmp_path / "Dev.v"
    src.write_text("Lemma a : True.\nProof.\nAdmitted.\n", encoding="utf-8")
    node = Node(id="a", name="a", statement="Lemma a : True.", parent=None)
    text = render_decomposition_task(node, Development(src))

    assert "Prefer more, smaller obligations" in text
    assert "fifty tactics" in text


def test_a_failed_obligation_reads_as_a_granularity_verdict() -> None:
    """A failure must reach the orchestrator as "this was not tightly scoped", not as
    a raw error dump. The provers are competent at small obligations and demonstrably
    fail on ones that bundle several steps, so a failure is first evidence about the
    statement."""
    from pcp.orch.prove import _design_evidence
    from pcp.orch.schedule import NodeOutcome, RunReport

    report = RunReport()
    report.outcomes = [
        NodeOutcome(node_id="1", name="big", status="stuck", attempts=2, elapsed_s=1200,
                    evidence="worker exceeded its 1200s deadline and was killed"),
        NodeOutcome(node_id="2", name="ok", status="qed", attempts=1, elapsed_s=90),
    ]
    text = _design_evidence(report)

    assert "1 of 2 obligations were not proved" in text
    assert "tightly scoped proof engineering" in text
    assert "split the failing obligations further" in text
    assert "this obligation is too large" in text


def test_a_contested_statement_is_not_reported_as_a_granularity_problem() -> None:
    """Splitting a statement the prover believes is false does not help anyone."""
    from pcp.orch.prove import _why_it_failed
    from pcp.orch.schedule import NodeOutcome

    verdict = _why_it_failed(NodeOutcome(
        node_id="1", name="c", status="contested", attempts=1,
        evidence="the frozen statement omits the £ 1 its sibling carries"))
    assert "statement itself is wrong" in verdict
    assert "too large" not in verdict


def test_repeated_independent_failures_are_evidence_about_the_statement() -> None:
    from pcp.orch.prove import _why_it_failed
    from pcp.orch.schedule import NodeOutcome

    verdict = _why_it_failed(NodeOutcome(node_id="1", name="x", status="stuck",
                                         attempts=3, evidence="iApply failed"))
    assert "evidence about the obligation, not the prover" in verdict


def test_the_decomposer_is_given_the_standard_up_front(tmp_path) -> None:
    from pcp.orch.assemble import Development
    from pcp.orch.decomposer import render_amendment_task, render_decomposition_task
    from pcp.orch.graph import Node

    src = tmp_path / "Dev.v"
    src.write_text("Lemma a : True.\nProof.\nAdmitted.\n", encoding="utf-8")
    node = Node(id="a", name="a", statement="Lemma a : True.", parent=None)

    assert "tightly scoped proof engineering" in render_decomposition_task(node, Development(src))
    amended = render_amendment_task(node, Development(src), design=[], evidence="x", round_no=2)
    assert "not tightly scoped" in amended
    assert "split it into smaller obligations before you touch the design" in amended


def test_a_malformed_amendment_is_re_asked_not_fatal() -> None:
    """A missing JSON field must not end the run as "no usable design".

    `seqlock_design` died exactly here with 2.5 hours of its wall unspent: the design
    did not compile, the amendment that would have fixed it came back with
    `design entry 'bcaf2' has no text`, and the rung reported "no proposed design was
    usable, so nothing can be proved against one" -- a claim about the design space,
    made on the strength of an unreadable answer.  The compile error is the same
    question either way, so re-asking costs one decomposer call and buys back a round.
    """
    from pcp.orch.prove import _amend_evidence
    from pcp.orch.decomposer import DecompositionResult

    rejected = DecompositionResult(problems=["design entry 'bcaf2' has no text"])
    assert not rejected.ok

    first = _amend_evidence("the design does not compile: unresolved implicit", None)
    assert first == "the design does not compile: unresolved implicit"

    second = _amend_evidence("the design does not compile: unresolved implicit", rejected)
    # The amender must see both what it has to fix and why its last answer bounced.
    assert "does not compile" in second
    assert "bcaf2" in second
    assert "needs both a `name` and a `text`" in second


def test_an_amendment_that_cannot_run_at_all_still_stops() -> None:
    """Re-asking is for unreadable answers, not for a provider that is down.

    Retrying an outage burns the wall to no purpose -- that is what the ladder's own
    outage halt exists to prevent -- so `infrastructure` breaks the retry loop.
    """
    from pcp.orch.decomposer import DecompositionResult

    outage = DecompositionResult(violation="401 OAuth access token has been revoked",
                                 infrastructure=True)
    assert not outage.ok and outage.infrastructure
    assert "could not run at all" in outage.render()
