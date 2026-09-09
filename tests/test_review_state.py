"""Wave-3 adversarial review of the state layer, offline part (no Rocq needed).

Each test is a defect that was reproduced against the rewritten code before the fix:
the ledger attributing an anonymous hypothesis by its *positional* id, a rename
permutation reported as two certain updates, a persistent hypothesis opened at every
step reported "never used", the "total" skeleton parser escaping with RecursionError,
a legacy event line crashing ``Trace.loads``, a shelved existential blamed on a
bullet, and the wrapper script under concurrent cold starts.
"""

from __future__ import annotations

import os
import shutil
import tempfile
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path

import pytest

from pcp.errors import StateError
from pcp.state.explain import Located, _no_tactic_failed, explain
from pcp.state.ipm.model import Hyp, IrisGoal, Step, scan_modality
from pcp.state.ipm.pattern import PatternSyntaxError, align, parse_pattern
from pcp.state.ipm.skeleton import parse_skeleton
from pcp.state.ledger.diff import diff_context, diff_step
from pcp.state.ledger.query import blame, unused_at_qed, where_did_it_go
from pcp.state.petanque import StateHandle, pet_wrapper, wrap_timeout
from pcp.state.render import render_goal
from pcp.state.session import StepResult
from pcp.state.trace import Trace, Tracer
from pcp.util.proc import run


def _goal(
    spatial: list[tuple[str, str]] = (),  # type: ignore[assignment]
    *,
    intuit: list[tuple[str, str]] = (),  # type: ignore[assignment]
    pure: list[tuple[str, str]] = (),  # type: ignore[assignment]
    goal: str = "Q",
    gid: str = "g0",
    anon: set[str] = frozenset(),  # type: ignore[assignment]
) -> IrisGoal:
    return IrisGoal(
        goal_id=gid,
        spatial=[Hyp(n, p, anonymous=n in anon) for n, p in spatial],
        intuitionistic=[Hyp(n, p, klass="intuitionistic") for n, p in intuit],
        pure=[Hyp(n, p, klass="pure") for n, p in pure],
        goal=goal,
    )


def _kinds(events) -> list[tuple[str, str | None]]:
    return [(e.kind, e.hyp) for e in events]


# ------------------------------------------------------------------ ledger honesty


def test_anonymous_hypotheses_match_by_prop_not_positional_id() -> None:
    """`_1`, `_2` are positions: spending `_1` shifts `_2` into its slot.

    Reproduced live (`iIntros "[? ?]". iAssert P with "[$]" as "HP".`): the diff said
    ``Update _1, Consume _2 -> HP`` while `_1` (P) became HP and `_2` (Q) became `_1`.
    """
    prev = [_goal([("_1", "P"), ("_2", "Q")], anon={"_1", "_2"})]
    nxt = [_goal([("_1", "Q"), ("HP", "P")], anon={"_1"})]
    events = diff_step(prev, nxt, step=2, tactic='iAssert P with "[$]" as "HP".')
    assert {e.kind for e in events} == {"Rename"}, _kinds(events)
    assert {(e.sources[0], e.hyp) for e in events} == {("_2", "_1"), ("_1", "HP")}
    assert all(e.confidence == "certain" for e in events)


def test_anonymous_hypothesis_spent_first_is_a_rename_of_the_survivor() -> None:
    prev = [_goal([("_1", "P"), ("_2", "Q")], anon={"_1", "_2"}, goal="R ∗ P")]
    nxt = [_goal([("_1", "Q")], anon={"_1"}, goal="R")]
    events = diff_step(prev, nxt, step=1, tactic="iFrame.")
    assert ("Update", "_1") not in _kinds(events)
    assert ("Frame", "_1") in _kinds(events) and ("Rename", "_1") in _kinds(events)
    rename = next(e for e in events if e.kind == "Rename")
    assert rename.sources == ["_2"]


def test_untouched_identical_anonymous_hypotheses_are_unchanged_not_unknown() -> None:
    hyps = [Hyp("_1", "P", anonymous=True), Hyp("_2", "P", anonymous=True)]
    d = diff_context(hyps, [Hyp("_1", "P", anonymous=True), Hyp("_2", "P", anonymous=True)])
    assert set(d.unchanged) == {"_1", "_2"} and not d.ambiguous and not d.renamed
    # One of two identical anonymous `P`s spent: the survivor keeps `_1`, nothing is uncertain.
    d = diff_context(hyps, [Hyp("_1", "P", anonymous=True)])
    assert d.unchanged == ("_1",) and d.consumed == ("_2",) and not d.ambiguous


def test_rename_permutation_is_unknown_not_two_certain_updates() -> None:
    """Reproduced live with three `iRename`s in one step: the printed state of a swap is
    indistinguishable from two updates, so the honest answer is `unknown`."""
    prev = [_goal([("H1", "P"), ("H2", "Q")])]
    nxt = [_goal([("H2", "P"), ("H1", "Q")])]
    events = diff_step(prev, nxt, step=2, tactic='iRename "H1" into "Ht". iRename "H2" into "H1". iRename "Ht" into "H2".')
    assert {e.kind for e in events} == {"Unknown"} and {e.hyp for e in events} == {"H1", "H2"}
    assert all(e.confidence == "unknown" for e in events)


def test_a_genuine_update_and_a_specialize_that_consumes_stay_certain() -> None:
    events = diff_step([_goal([("H1", "P -∗ Q"), ("H2", "R")])], [_goal([("H1", "Q"), ("H2", "R")])], step=1, tactic="x.")
    assert _kinds(events) == [("Update", "H1")]
    # HW's new prop equals HP's old prop, but HP was consumed, not updated: no permutation.
    events = diff_step([_goal([("HW", "P -∗ P"), ("HP", "P")])], [_goal([("HW", "P")])], step=1, tactic='iSpecialize ("HW" with "HP").')
    assert ("Update", "HW") in _kinds(events) and ("Consume", "HP") in _kinds(events)
    assert all(e.confidence == "certain" for e in events)


@dataclass
class _TraceLike:
    steps: list[Step]
    events: list = field(default_factory=list)


def test_named_persistent_hypothesis_use_is_recorded_so_unused_at_qed_is_honest() -> None:
    """Reproduced on `Basic.inv_open`: `iInv "Hinv"` produced HP/Hclose with no source
    and `unused_at_qed` listed the invariant that every step depended on."""
    s0 = _goal(intuit=[("Hinv", "inv N P")], goal="|={⊤}=> True")
    s1 = _goal([("HP", "▷ P"), ("Hclose", "▷ P ={⊤ ∖ ↑N,⊤}=∗ True")], intuit=[("Hinv", "inv N P")], goal="|={⊤ ∖ ↑N,⊤}=> True")
    s2 = _goal(intuit=[("Hinv", "inv N P")], goal="|={⊤}=> True")
    steps = [
        Step(0, 1, "<start>", [s0]),
        Step(1, 2, 'iInv "Hinv" as "HP" "Hclose".', [s1]),
        Step(2, 3, 'iMod ("Hclose" with "HP") as "_".', [s2]),
        Step(3, 4, "done.", []),
    ]
    trace = _TraceLike(steps)
    assert unused_at_qed(trace) == []
    use = next(e for e in diff_step([s0], [s1], step=1, tactic=steps[1].tactic) if e.hyp == "Hinv")
    assert use.kind == "Frame" and use.klass == "intuitionistic" and use.targets == ["HP", "Hclose"]
    assert use.confidence == "certain" and "stays available" in use.detail
    prov = where_did_it_go(trace, "Hinv")
    assert prov.fate == "live" and "never consumed" in prov.note
    # Closing a goal by applying a persistent hypothesis is a use too ...
    closing = diff_step([_goal(intuit=[("HP", "P")], goal="P")], [], step=1, tactic='iApply "HP".')
    assert ("Frame", "HP") in _kinds(closing)
    # ... but naming it in a step that did nothing is not.
    same = _goal(intuit=[("HP", "P")], goal="P")
    assert _kinds(diff_step([same], [same], step=1, tactic='iDestruct "HP" as "HP".')) == []


def test_split_targets_include_the_pure_names_left_behind() -> None:
    prev = [_goal([("H", "∃ n, ⌜n = 3⌝ ∗ Φ n")], goal="Φ 3")]
    nxt = [_goal([("HΦ", "Φ n")], pure=[("n", "nat"), ("Hn", "n = 3")], goal="Φ 3")]
    tactic = 'iDestruct "H" as (n) "[%Hn HΦ]".'
    events = diff_step(prev, nxt, step=2, tactic=tactic)
    consume = next(e for e in events if e.kind == "Consume")
    assert consume.targets == ["HΦ", "n", "Hn"]
    trace = _TraceLike([Step(0, 1, "<start>", prev), Step(1, 2, tactic, nxt), Step(2, 3, 'iApply "H".', nxt, ok=False, error="H not found")])
    assert '"HΦ", "n", "Hn"' in blame(trace, 2, "H").advice


# --------------------------------------------------------------- parser totality


def test_parse_skeleton_is_total_under_deep_nesting() -> None:
    assert parse_skeleton("(" * 3000 + "P" + ")" * 3000).kind == "atom"
    assert parse_skeleton(" ∗ ".join(["P"] * 5000)).kind == "atom"
    assert parse_skeleton("▷ " * 5000 + "P").kind == "atom"


def test_a_pattern_nested_past_the_stack_is_a_syntax_error_not_a_crash() -> None:
    for text in ("[" * 5000 + "H" + "]" * 5000, "#" * 5000 + "H", "[H " * 3000 + "H" + "]" * 3000):
        with pytest.raises(PatternSyntaxError):
            parse_pattern(text)
        with pytest.raises(PatternSyntaxError):
            align(text, "P ∗ Q")


# ------------------------------------------------------------------ trace artifact


def test_trace_loads_a_legacy_event_line_without_rec_or_confidence() -> None:
    text = (
        '{"v":1,"file":"f","thm":"t","props":{}}\n'
        '{"v":1,"step":0,"state_id":1,"tactic":"<start>","goals":[]}\n'
        '{"step":1,"kind":"Consume","tactic":"iFrame.","hyp":"H"}\n'
    )
    trace = Trace.loads(text)
    assert len(trace.steps) == 1 and len(trace.events) == 1 and trace.events[0].kind == "Consume"


def test_step_messages_survive_the_jsonl_round_trip() -> None:
    step = Step(1, 2, "iDump.", [], messages=['PCP1\tspatial\t(INamed "H")\tP'])
    assert Step.from_json(step.to_json()).messages == step.messages
    assert "messages" not in Step(1, 2, "idtac.", []).to_json()


class _FakeSession:
    source_file = file = "/nowhere/F.v"
    thm = "t"

    def __init__(self) -> None:
        self.n = 1

    def start(self) -> StateHandle:
        return StateHandle(process=1, generation=0, st=1, state_hash=1)

    def run(self, tactic: str, *, timeout: float | None = None) -> StepResult:
        if tactic == "bad.":
            return StepResult(ok=False, error="Coq: no", tactic=tactic)
        self.n += 1
        return StepResult(ok=True, state=StateHandle(1, 0, self.n, state_hash=self.n), state_hash=self.n, tactic=tactic)

    def goals(self, state: StateHandle | None = None) -> list:
        return []


def test_a_later_success_clears_the_trace_error_but_keeps_the_failed_step() -> None:
    tracer = Tracer(_FakeSession())  # type: ignore[arg-type]
    tracer.start()
    tracer.start()  # idempotent: one step 0 (legacy: a second `<start>` step)
    assert [s.step for s in tracer.trace.steps] == [0]
    assert not tracer.step("bad.").ok and tracer.trace.failed_at == 1 and tracer.trace.error
    assert tracer.step("idtac.").ok
    assert tracer.trace.failed_at is None and tracer.trace.error is None
    assert [s.ok for s in tracer.trace.steps] == [True, False, True] and tracer.trace.steps[2].step == 2


# ------------------------------------------------------------------------ explain


def test_a_shelved_existential_is_not_blamed_on_a_bullet() -> None:
    located = Located("ev2", 0, 10)
    shelved = _no_tactic_failed(located, ["a.", "b."], False, True, no_goals_shown=True)
    assert "shelved" in shelved and "Unshelve" in shelved and "bullet" not in shelved
    open_goal = _no_tactic_failed(located, ["a.", "b."], False, True, no_goals_shown=False)
    assert "bullet or brace" in open_goal


def test_explain_bounds_petanque_start_by_its_budget(monkeypatch, tmp_path: Path) -> None:
    """`pcp check`'s replay builds its own pool: `petanque/start` must sit under the wall
    budget too, not under the 600 s default (a wedged start ate ten minutes of the clock)."""
    seen: dict[str, object] = {}

    class FakePool:
        def __init__(self, workspace, size=2, **cfg) -> None:
            seen.update(cfg)

        def open(self, *args, **kwargs):
            raise StateError("no pet in this test")

        def close(self) -> None:
            seen["closed"] = True

    monkeypatch.setattr("pcp.state.pool.SessionPool", FakePool)
    monkeypatch.setattr("pcp.state.explain.petanque_available", lambda: True)
    text = "Lemma x : True.\nProof. exact I. exact I. Qed.\n"
    output = 'File "./X.v", line 2, characters 16-24:\nError: No such goal.'
    out = explain(assembly_text=text, assembled_path_name="X.v", compile_output_or_result=output, root=tmp_path,
                  target="x", budget_seconds=7, verbose=True)
    assert "could not run" in out and seen.get("closed") is True
    assert isinstance(seen["start_timeout"], float) and 7 <= seen["start_timeout"] <= 60
    assert not list(tmp_path.glob("*__pcp*"))


# ------------------------------------------------------------------- petanque bits


def test_wrap_timeout_skips_bullets_braces_and_already_timed_sentences() -> None:
    src = '- iIntros "H". { iFrame. } 2: { done. } all: idtac. Timeout 3 idtac. } + idtac...'
    text, n = wrap_timeout(src, 5)
    assert text == (
        '- Timeout 5 iIntros "H". { Timeout 5 iFrame. } 2: { Timeout 5 done. } Timeout 5 all: idtac. '
        "Timeout 3 idtac. } + Timeout 5 idtac..."
    )
    assert n == 5


def test_modality_is_read_at_the_head_only_and_wp_is_a_token() -> None:
    assert scan_modality("⌜wp = 1⌝").wp is None
    wand = scan_modality("P -∗ |={⊤}=> Q")
    assert not wand.fupd and wand.mask is None
    twp = scan_modality("WP e @ NotStuck; ⊤ ∖ ↑N [{ Φ }]")
    assert twp.wp is not None and twp.wp.total and twp.mask == "⊤ ∖ ↑N"


# ------------------------------------------------------------------------- render


def test_render_footer_is_honest_under_a_zero_budget() -> None:
    goal = _goal([("Hl", "l ↦ v"), ("H", "∃ x, P x ∗ Q")], intuit=[("Hinv", "inv N P")], goal="WP e {{ Φ }}")
    r = render_goal(goal, budget=0)
    assert r.shown == 0 and r.elided == ["Hinv", "Hl", "H"] and r.tokens > 0
    assert r.text.splitlines()[-1].startswith("rendered 0/3 hypotheses") and "3 elided" in r.text
    # An explicit selection that does not fit is *elided* (visible), never silently unselected.
    r = render_goal(goal, budget=5, select="Hl")
    assert r.elided == ["Hl"] and "Hl" not in r.manifest and "budget exhausted, omitted: Hl" in r.text


# ------------------------------------------------------------------------ wrapper


def test_wrapper_is_created_atomically_under_concurrent_cold_starts() -> None:
    """Twelve cold processes create the same wrapper at once and every one execs it."""
    limit = 100_000 + os.getpid() % 50_000
    root = Path(tempfile.gettempdir()) / f"pcp-pet-{os.getuid()}-{limit}"
    shutil.rmtree(root, ignore_errors=True)
    code = (
        "from pcp.state.petanque import pet_wrapper; from pcp.util.proc import run; "
        f"w = pet_wrapper('/bin/echo', {limit}); print(run([str(w), 'hi']).stdout.strip())"
    )
    env = {**os.environ, "PYTHONPATH": str(Path(__file__).resolve().parents[1])}
    try:
        with ThreadPoolExecutor(max_workers=12) as pool:
            results = list(pool.map(lambda _: run([os.sys.executable, "-c", code], env=env, timeout=60), range(12)))
        assert all(r.ok and r.stdout.strip() == "hi" for r in results), [(r.returncode, r.stderr[-200:]) for r in results]
        wrapper = pet_wrapper("/bin/echo", limit)
        assert wrapper.parent == root and oct(wrapper.parent.stat().st_mode & 0o777) == "0o700"
        assert os.access(wrapper, os.X_OK) and str(os.getuid()) in str(wrapper)
    finally:
        shutil.rmtree(root, ignore_errors=True)
