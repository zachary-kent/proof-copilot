"""Tactic effects (pcp.state.ledger.effects, D2 / missing feature 4): what a step did to
the goal -- goals created and their order, rewrite sites and occurrences, iFrame's closed
conjuncts and witnesses, evars, and where ``wp_pures`` stopped -- with ``unknown`` when
the printed states do not say."""

from __future__ import annotations

import json
from collections import defaultdict

import pytest
from conftest import GOLDENS, needs_goldens

from pcp.state.ipm.model import Hyp, IrisGoal, Step
from pcp.state.ipm.parse import parse_goal
from pcp.state.ledger.diff import attach, replay_events, step_events
from pcp.state.ledger.effects import _effects, effect_lines, step_effects
from pcp.state.ledger.events import EFFECT_KINDS, Event
from pcp.state.ledger.query import where_did_it_go
from pcp.state.redex import next_redex, wp_expr
from pcp.state.terms import changes, evars, match_template, substitute


def state(gid: str, goal: str, *, spatial=(), pure=(), intuit=(), ipm: bool = True) -> IrisGoal:
    return IrisGoal(
        goal_id=gid, goal=goal, is_ipm=ipm,
        spatial=[Hyp(i, p) for i, p in spatial],
        pure=[Hyp(i, p, klass="pure") for i, p in pure],
        intuitionistic=[Hyp(i, p, klass="intuitionistic") for i, p in intuit],
    )


def effects(prev, next_, tactic):
    return step_effects(prev, next_, step=3, tactic=tactic)


def one(events, kind):
    got = [e for e in events if e.kind == kind]
    assert len(got) == 1, [e.render() for e in events]
    return got[0]


# ------------------------------------------------------------------- terms


def test_match_template_binds_balanced_subterms_consistently() -> None:
    assert match_template("P x ∗ Q", {"x"}, "P (S n) ∗ Q") == {"x": "S n"}
    assert match_template("l ↦ ?v ∗ own γ ?v", {"?v"}, "l ↦ #3 ∗ own γ #3") == {"?v": "#3"}
    assert match_template("l ↦ ?v ∗ own γ ?v", {"?v"}, "l ↦ #3 ∗ own γ #4") is None
    assert match_template("P x", {"x"}, "Q y") is None
    # `x` never matches inside `xs`: tokens, not characters.
    assert substitute("P x xs", {"x": "S n"}) == "P (S n) xs"
    assert substitute("P x", {"x": "#3"}) == "P #3"


def test_changes_are_balanced_sites_in_the_before_term() -> None:
    (c,) = changes("P (x + 0) ∗ Q (x + 0)", "P x ∗ Q (x + 0)")
    assert (c.old, c.new, c.at) == ("(x + 0)", "x", 1)
    assert [(c.old, c.new) for c in changes("n + 0 = m", "n = m")] == [("n + 0", "n")]
    assert [(c.old, c.new) for c in changes("length vs = n", "length (v :: vs') = n")] == [("vs", "(v :: vs')")]


def test_conditional_modality_flags_are_not_evars() -> None:
    assert evars("▷?q P ∗ own γ ?x ∗ □?p Q") == ["?x"]


# --------------------------------------------------------------- goals order


def test_side_goals_are_listed_in_order_with_their_shapes() -> None:
    prev = [state("g0", "WP f #() {{ v, Φ v }}")]
    next_ = [state("g0", "WP #() {{ v, Φ v }}"), state("g1", "⌜n < length vs⌝"), state("g2", "0 ≤ n", ipm=False)]
    e = one(effects(prev, next_, 'wp_apply (f_spec with "H").'), "GoalsCreated")
    assert e.targets == ["g0", "g1", "g2"]
    assert e.detail.startswith("one goal became 3, in order: [1] g0: `WP #() {{ v, Φ v }}`; [2] g1: `⌜n < length vs⌝` "
                               "(pure side condition); [3] g2: `0 ≤ n` (pure side condition)"), e.detail
    assert [g["side"] for g in e.data["goals"]] == [False, True, True]


def test_case_split_goals_with_equal_conclusions_are_told_apart_by_their_hypotheses() -> None:
    prev = [state("g0", "WP e {{ Φ }}", spatial=[("Hc", "c ↦ v")])]
    next_ = [state("g0", "WP e {{ Φ }}", spatial=[("Hc", "c ↦ InjLV #()")]),
             state("g1", "WP e {{ Φ }}", spatial=[("Hc", "c ↦ InjRV #b")])]
    e = one(effects(prev, next_, 'iDestruct "Hc" as "[Hc|Hc]".'), "GoalsCreated")
    assert "[1] g0: `WP e {{ Φ }}` with Hc : c ↦ InjLV #()" in e.detail
    assert "[2] g1: `WP e {{ Φ }}` with Hc : c ↦ InjRV #b" in e.detail


def test_closing_a_goal_says_which_goal_is_focused_next() -> None:
    e = one(effects([state("g0", "P"), state("g1", "Q ∗ R")], [state("g0", "Q ∗ R")], "done."), "Focus")
    assert e.detail == "the focused goal closed; now focused: g0 `Q ∗ R`"


# ------------------------------------------------------------------- rewrite


def test_rewrite_names_the_occurrence_and_what_remains() -> None:
    e = one(effects([state("g0", "P (x + 0) ∗ Q (x + 0)")], [state("g0", "P x ∗ Q (x + 0)")], "rewrite Nat.add_0_r."), "Rewrite")
    assert e.hyp is None and e.data["target"] == "goal"
    assert e.detail == ("in the goal: `(x + 0)` → `x` (occurrence 1 of 2); "
                        "1 other occurrence of `(x + 0)` remains")
    every = one(effects([state("g0", "P (x + 0) ∗ Q (x + 0)")], [state("g0", "P x ∗ Q x")], "rewrite !Nat.add_0_r."), "Rewrite")
    assert every.detail == "in the goal: `(x + 0)` → `x` (all 2 occurrences)"


def test_rewrite_in_a_hypothesis_names_it_and_ignores_occurrences_inside_the_result() -> None:
    prev = [state("g0", "R", pure=[("Hn", "n = length vs")])]
    next_ = [state("g0", "R", pure=[("Hn", "n = length (v :: vs)")])]
    e = one(effects(prev, next_, "rewrite Hvs in Hn."), "Rewrite")
    # `vs` still occurs after, but only inside the replacement: nothing was left behind.
    assert e.hyp == "Hn" and e.detail == 'in "Hn": `vs` → `(v :: vs)` (its only occurrence)'


def test_rewrite_that_changed_nothing_visible_is_unknown() -> None:
    e = one(effects([state("g0", "P x")], [state("g0", "P x", pure=[])], "rewrite H."), "Rewrite")
    assert e.confidence == "unknown" and "no printed term changed" in e.detail


# -------------------------------------------------------------------- iFrame


def test_iframe_reports_closed_conjuncts_the_hypothesis_for_each_and_the_witness() -> None:
    prev = [state("g0", "∃ v, l ↦ v ∗ own γ v ∗ Q", spatial=[("Hl", "l ↦ #3"), ("Ho", "own γ #3"), ("HR", "R")])]
    next_ = [state("g0", "Q", spatial=[("HR", "R")])]
    ev = effects(prev, next_, "iFrame.")
    w = one(ev, "Witness")
    assert w.detail == "the goal's `∃ v` was instantiated with `#3`" and w.data == {"binder": "v", "value": "#3"}
    f = one(ev, "FrameClosed")
    assert f.detail == 'closed `l ↦ #3` with "Hl", `own γ #3` with "Ho"; spent "Hl", "Ho"'
    assert f.data["closed"] == [{"conjunct": "l ↦ #3", "by": "Hl"}, {"conjunct": "own γ #3", "by": "Ho"}]


def test_iframe_instantiating_an_evar_reads_its_value_off_the_spent_hypothesis() -> None:
    ev = effects([state("g0", "l ↦ ?v ∗ Q", spatial=[("Hl", "l ↦ #3")])], [state("g0", "Q")], 'iFrame "Hl".')
    assert one(ev, "EvarInstantiated").detail == '`?v` := `#3` (read off "Hl")'
    assert one(ev, "FrameClosed").detail == 'closed `l ↦ #3` with "Hl"; spent "Hl"'


def test_evar_instantiated_in_place_and_unknown_when_not_visible() -> None:
    got = one(effects([state("g0", "own γ ?x ∗ P")], [state("g0", "own γ (q / 2) ∗ P")], "iPureIntro."), "EvarInstantiated")
    assert got.detail == "`?x` := `q / 2` (read off the goal)"
    lost = one(effects([state("g0", "own γ ?x ∗ P")], [state("g0", "Q")], "iApply H."), "EvarInstantiated")
    assert lost.confidence == "unknown" and lost.data["value"] is None


def test_iexists_witness_from_the_goal_or_the_tactic_and_none_for_a_replaced_goal() -> None:
    w = one(effects([state("g0", "∃ x, P x")], [state("g0", "P (S n)")], "iExists (S n)."), "Witness")
    assert w.detail == "the goal's `∃ x` was instantiated with `S n`"
    told = one(effects([state("g0", "∃ x, P x")], [state("g0", "R ∗ Q")], "iExists (S n); iSplit."), "Witness")
    assert told.detail == "the goal's `∃ x` was instantiated with `S n` (as given in the tactic)"
    # An iApply that replaced the goal did not instantiate the ∃: nothing is claimed.
    assert not [e for e in effects([state("g0", "∃ x, P x")], [state("g0", "Q")], 'iApply "H".') if e.kind == "Witness"]
    # Alpha-renaming (`∃ x` -> `∃ x0`) is not an instantiation either.
    assert not [e for e in effects([state("g0", "∃ x, P x")], [state("g0", "∃ x0, P x0")], "iIntros.") if e.kind == "Witness"]


# ------------------------------------------------------------------ wp_pures


@pytest.mark.parametrize(("goal", "kind", "text", "next_"), [
    ('WP let: "o" := ! #lo in "o" {{ v, Φ v }}', "heap", "! #lo", "wp_load"),
    ("WP if: #(bool_decide (#x = #o)) then #() else f #x {{ v, Φ v }}", "branch", "if: #(bool_decide (#x = #o)) then …",
     "case_bool_decide"),
    ("WP acquire (#lo, #ln)%V {{ v, Φ v }}", "call", "acquire (#lo, #ln)%V", "wp_apply"),
    ("WP #lo <- #(o + 1) {{ v, Φ v }}", "heap", "#lo <- #(o + 1)", "wp_store"),
    ("WP if: Snd (CmpXchg #l #c #(1 + c)) then #() else incr #l {{ v, Φ v }}", "heap", "CmpXchg #l #c #(1 + c)",
     "wp_cmpxchg (or wp_cmpxchg_suc / wp_cmpxchg_fail)"),
    ('WP match: v with InjL <> => #() | InjR "x" => "x" end @ E {{ v, Φ v }}', "match", "match: v with …", ""),
    ("▷ WP Snd v {{ v, Φ v }}", "opaque", "Snd v", ""),
    ("WP if: #b then #1 else #2 {{ v, Φ v }}", "branch", "if: #b then …", "destruct b"),
])
def test_next_redex_finds_the_evaluation_position(goal: str, kind: str, text: str, next_: str) -> None:
    expr = wp_expr(goal)
    assert expr is not None
    red = next_redex(expr)
    assert (red.kind, red.text, red.next) == (kind, text, next_)


def test_wp_expr_only_at_the_head() -> None:
    assert wp_expr("P -∗ WP ! #l {{ v, Φ v }}") is None
    assert wp_expr("|={⊤}=> Φ #true") is None
    assert wp_expr("|={⊤}=> ▷ WP ! #l @ E {{ v, Φ v }}") == "! #l"


def test_wp_pures_stop_names_the_redex_why_and_a_missing_points_to() -> None:
    prev = [state("g0", 'WP let: "o" := #lo in ! "o" {{ v, Φ v }}', spatial=[("H", "lo ↦ #1")])]
    have = one(effects(prev, [state("g0", "WP ! #lo {{ v, Φ v }}", spatial=[("H", "lo ↦ #1")])], "wp_pures."), "WpStop")
    assert have.detail == "stopped at `! #lo`: a load: `wp_pures` only takes pure steps; `wp_load` steps it"
    assert have.data["kind"] == "heap" and have.confidence == "certain"
    lacking = one(effects(prev, [state("g0", "WP ! #lo {{ v, Φ v }}")], "wp_pures."), "WpStop")
    assert "there is no `lo ↦ …` in the context yet" in lacking.detail
    undecided = one(effects([state("g0", "WP #x = #o {{ Φ }}")], [state("g0", "WP if: #(bool_decide (x = o)) then #1 else #2 {{ Φ }}")],
                            "wp_pures."), "WpStop")
    assert "`bool_decide (x = o)` is undecided" in undecided.detail and "case_bool_decide" in undecided.detail
    value = one(effects([state("g0", "WP #1 + #1 {{ v, Φ v }}")], [state("g0", "|={⊤}=> Φ #2")], "wp_pures."), "WpStop")
    assert value.detail == "the program reduced to a value; the goal is now `|={⊤}=> Φ #2`"


def test_wp_pures_stop_it_cannot_explain_is_unknown() -> None:
    e = one(effects([state("g0", "WP e1 {{ Φ }}")], [state("g0", 'WP "x" {{ Φ }}')], "wp_pures."), "WpStop")
    assert e.confidence == "unknown" and "why is unknown" in e.detail


# ------------------------------------------------------------- the event log


def test_effect_events_round_trip_and_render() -> None:
    ev = effects([state("g0", "P (x + 0)")], [state("g0", "P x")], "rewrite H.")
    back = [Event.from_json(json.loads(json.dumps(e.to_json()))) for e in ev]
    assert [b.data for b in back] == [e.data for e in ev] and back[0].klass == "effect"
    assert effect_lines(ev) == ["Rewrite: in the goal: `(x + 0)` → `x` (its only occurrence)"]
    # Resource events carry no `data` key: the v=1 record shape is unchanged for them.
    assert "data" not in Event(step=1, kind="Intro", tactic="t.", hyp="H").to_json()


def test_attach_and_replay_record_effects_beside_resource_events() -> None:
    s0 = Step(step=0, state_id=0, tactic="<start>", goals=[state("g0", "P (x + 0)", spatial=[("H", "Q")])])
    s1 = Step(step=1, state_id=1, tactic="rewrite Nat.add_0_r.", goals=[state("g0", "P x", spatial=[("H", "Q")])])
    kinds = [e.kind for e in replay_events([s0, s1])]
    assert kinds == [e.kind for e in step_events(s0.goals, s1.goals, step=1, tactic=s1.tactic)] and "Rewrite" in kinds

    class _Tracer:
        trace = _Trace([], [])
        on_step = None

    tracer = attach(_Tracer())
    tracer.on_step(s1, s0.goals)
    assert [e.kind for e in tracer.trace.events] == ["Rewrite"]


def test_effects_never_raise_and_never_set_a_fate() -> None:
    class Boom(IrisGoal):
        @property
        def all_hyps(self):  # type: ignore[override]
            raise RuntimeError("boom")

    assert step_effects([Boom(goal="P x")], [Boom(goal="P y")], step=1, tactic="rewrite H.") == []

    # A `Rewrite` of "H" with confidence unknown must not make H's provenance unknown.
    steps = [Step(step=0, state_id=0, tactic="<start>", goals=[state("g0", "P", spatial=[("H", "Q")])]),
             Step(step=1, state_id=1, tactic="rewrite X in H.", goals=[state("g0", "P", spatial=[("H", "Q'")])])]
    events = [Event(step=1, kind="Update", tactic="rewrite X in H.", hyp="H"),
              Event(step=1, kind="Rewrite", tactic="rewrite X in H.", hyp="H", confidence="unknown", klass="effect")]
    prov = where_did_it_go(_Trace(steps, events), "H")
    assert prov.fate == "live" and not [link for link in prov.forward if link.kind in EFFECT_KINDS]


class _Trace:
    def __init__(self, steps, events) -> None:
        self.steps, self.events = steps, events


# ------------------------------------------------------------------ goldens


@needs_goldens
def test_effects_over_the_golden_corpus_are_total_and_pinned() -> None:
    """Every consecutive pair of golden states: no crash, and the effects the issue list
    asked for come out on real Iris output."""
    rows = [json.loads(line) for line in GOLDENS.read_text(encoding="utf-8").splitlines() if line.strip()]
    by: dict[tuple, list[dict]] = defaultdict(list)
    for r in rows:
        by[(r["thm"], r["step"])].append(r)
    found: dict[tuple[str, int], list[str]] = {}
    for (thm, step), rs in by.items():
        prev = by.get((thm, step - 1))
        if not prev:
            continue
        pg = [parse_goal(r["ty"], r["hyps"], goal_id=f"g{r['goal_index']}") for r in sorted(prev, key=lambda r: r["goal_index"])]
        ng = [parse_goal(r["ty"], r["hyps"], goal_id=f"g{r['goal_index']}") for r in sorted(rs, key=lambda r: r["goal_index"])]
        found[(thm, step)] = effect_lines(_effects(pg, ng, step, rs[0]["tactic"]))  # the raising variant
    assert len(found) > 1000
    assert any("`bool_decide (#x = #o)` is undecided" in line for line in found[("wait_loop_spec", 28)])
    assert "Rewrite: in the goal: `newcounter` → `(λ: <>, ref #0)%V` (its only occurrence)" in found[("newcounter_contrib_spec", 2)]
    assert 'FrameClosed: closed `l ↦ #(i1 + i2)` with "Hl"; spent "Hl"' in found[("faa_spec", 19)]
    assert any(line.startswith("WpStop: stopped at `acquire (#lo, #ln)%V`: a call to `acquire`")
               for line in found[("acquire_spec", 43)])
