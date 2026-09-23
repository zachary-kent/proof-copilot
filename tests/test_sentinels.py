"""pcp.orch.sentinels: the free statement sentinels (PLAN.md 8.4)."""

from __future__ import annotations

from pcp.orch.sentinels import (
    SentinelHit,
    body_hash,
    hygiene_sentinel,
    is_lateral,
    partial_correctness,
    resources_outside_triple,
    run_free_sentinels,
    statement_body,
)
from pcp.rocq.assemble import NodeSpec
from pcp.rocq.statement import statement_hash

ROOT = "Lemma root (P Q : Prop) : P /\\ Q -> Q /\\ P."


def _hits(report, sentinel):
    return [h for h in report.hits if h.sentinel == sentinel]


def test_duplicate_among_the_plan_is_blocking_and_name_insensitive():
    specs = [NodeSpec("a", "Lemma a (P : Prop) : P -> P."), NodeSpec("b", "Polymorphic Lemma b (P : Prop) : P -> P.")]
    report = run_free_sentinels(specs, root_statement=ROOT)
    dup = _hits(report, "duplicate statement")
    assert len(dup) == 1 and dup[0].node == "b" and dup[0].blocking and "same statement as a" in dup[0].detail
    assert not report.ok


def test_duplicate_against_existing_hashes_by_either_hash():
    spec = NodeSpec("s", "Lemma s : nat -> nat.")
    by_body = {body_hash("Lemma zz : nat -> nat."): "zz"}
    assert _hits(run_free_sentinels([spec], existing_hashes=by_body), "duplicate statement")[0].detail == "same statement as zz"
    by_text = {statement_hash("Lemma s : nat -> nat.")}
    assert _hits(run_free_sentinels([spec], existing_hashes=by_text), "duplicate statement")


def test_child_restating_the_root_is_a_lateral_move():
    report = run_free_sentinels([NodeSpec("r2", "Lemma r2 (P Q : Prop) : P /\\ Q -> Q /\\ P.")], root_statement=ROOT)
    hit = _hits(report, "reduction sentinel")
    assert len(hit) == 1 and hit[0].blocking and not report.ok


def test_is_lateral_compares_bodies_not_names():
    assert is_lateral("Lemma helper (P : Prop) : P -> P.", "Lemma goal (P : Prop) : P -> P.")
    assert not is_lateral("Lemma helper (P : Prop) : P -> P.", "Lemma goal (P : Prop) : P -> P -> P.")


def test_converging_failure_against_stuck_statements():
    stuck = {"old": "Lemma old (P : Prop) : P -> P."}
    report = run_free_sentinels([NodeSpec("a", "Lemma a (P : Prop) : P -> P.")], stuck_statements=stuck)
    hit = _hits(report, "converging failure")
    assert hit and hit[0].blocking and "old" in hit[0].detail
    as_tuples = run_free_sentinels([NodeSpec("a", "Lemma a (P : Prop) : P -> P.")], stuck_statements=[("old", stuck["old"])])
    assert _hits(as_tuples, "converging failure")


def test_texan_triple_is_flagged_as_partial():
    hits = partial_correctness("c", "Lemma c l v : {{{ l ↦ v }}} !#l {{{ w, RET w; ⌜w = v⌝ }}}.")
    assert hits and not hits[0].blocking


def test_multiline_total_wp_is_not_flagged():
    assert partial_correctness("d", "Lemma d l v :\n l ↦ v -∗\n WP !#l\n [{ w, ⌜w = v⌝ }].") == []
    assert partial_correctness("e", "Lemma e : twp_x e.") == []
    assert partial_correctness("f", "Lemma f l v : [[{ l ↦ v }]] !#l [[{ w, RET w; True }]].") == []


def test_wp_in_a_comment_is_ignored_and_plain_wp_is_flagged():
    assert partial_correctness("e", "Lemma e : (* WP *) True.") == []
    assert partial_correctness("g", "Lemma g : ⊢ WP e {{ v, True }}.")


def test_hygiene_is_advisory_and_uses_explicit_binders():
    assert hygiene_sentinel("Lemma p (a : nat) : True.", "Lemma c (a b c d : nat) : True.", "c") == []
    hit = hygiene_sentinel("Lemma p (a : nat) : True.", "Lemma c (a b c d e : nat) {x : nat} : True.", "c")
    assert hit and not hit[0].blocking and "5 explicit binders" in hit[0].detail


def test_statement_body_strips_attributes_and_modifiers():
    assert statement_body("#[global] Local Lemma x (P : Prop) : P.") == statement_body("Lemma y (P : Prop) : P.")
    assert statement_body("Definition d := 1.") == "Definition d := 1."


def test_report_render_and_json():
    clean = run_free_sentinels([NodeSpec("a", "Lemma a : True.")])
    assert clean.ok and clean.render() == "sentinels: clean" and clean.to_json() == {"ok": True, "hits": []}
    report = run_free_sentinels([NodeSpec("a", "Lemma a : True."), NodeSpec("b", "Lemma b : True.")])
    assert report.render().startswith("sentinels:\n  [BLOCK] b: duplicate statement")
    assert report.to_json()["hits"][0] == SentinelHit("duplicate statement", "b", "same statement as a", True).to_json()


def test_a_non_persistent_wand_premise_before_a_texan_triple_is_a_blocking_hit() -> None:
    bad = ("Lemma c4_close l γₚ k ws Q : k `mod` 2 = 0 → inv N (I l) -∗ own γₚ (◯E ((S k, ws) : leibnizO _)) -∗ "
           "p16 γ ws Q -∗ {{{ True }}} #l <- #(S (S k)) {{{ RET #(); Q }}}.")
    hits = resources_outside_triple("c4_close", bad)
    assert len(hits) == 1 and hits[0].blocking and "◯E" in hits[0].detail
    # persistent premises, points-to inside the precondition, and no triple at all are fine
    assert resources_outside_triple("ok", "Lemma ok l v : inv N (I l) -∗ ⌜v = #0⌝ -∗ {{{ l ↦ v }}} !#l {{{ w, RET w; True }}}.") == []
    assert resources_outside_triple("wp", "Lemma wp l v : l ↦ v -∗ WP !#l {{ w, ⌜w = v⌝ }}.") == []
    assert resources_outside_triple("boxed", "Lemma b l v : □ (l ↦ v) -∗ {{{ True }}} !#l {{{ w, RET w; True }}}.") == []
    assert resources_outside_triple("frag", "Lemma f γ : own γ (◯ MaxNat 3) -∗ {{{ True }}} #() {{{ RET #(); True }}}.") == []


def test_a_design_defined_predicate_that_is_not_visibly_persistent_may_not_precede_a_triple() -> None:
    """Round 8 `c4_aux`: `p16 γ ws Q -∗ {{{ ... }}}` where p16 is a plain wand."""
    defs = {
        "p16": "Definition p16 (γ : gname) (ws : list val) (Q : iProp Σ) : iProp Σ := (∀ vs, own γ (◯E vs) ={⊤}=∗ Q).",
        "d15": "Definition d15 (l : loc) : iProp Σ := inv N (∃ v, l ↦ v).",
        "b14": "Definition b14 (γ : gname) : iProp Σ := □ (∀ n, own γ (◯ (MaxNat n)) -∗ True).",
    }
    st = "Lemma c4_aux l γ ws Q : length ws = 0 → d15 l -∗ p16 γ ws Q -∗ {{{ True }}} c4 #l {{{ RET #(); Q }}}."
    hits = resources_outside_triple("c4_aux", st, definitions=defs)
    assert len(hits) == 1 and hits[0].blocking and "p16" in hits[0].detail
    ok = "Lemma ok l γ : d15 l -∗ b14 γ -∗ {{{ True }}} c4 #l {{{ RET #(); True }}}."
    assert resources_outside_triple("ok", ok, definitions=defs) == []
    # the fixed shape: the resource is in the precondition
    fixed = "Lemma c4_aux l γ ws Q : length ws = 0 → d15 l -∗ {{{ p16 γ ws Q }}} c4 #l {{{ RET #(); Q }}}."
    assert resources_outside_triple("c4_aux", fixed, definitions=defs) == []


def test_a_design_predicate_as_an_argument_of_inv_is_not_a_resource_outside_the_triple() -> None:
    """Round 8 `x3_spec` was proved as stated: `inv N (d15 …) -∗ {{{ True }}} …`; the
    restatement path must not reject a sibling that stands."""
    defs = {"d15": "Definition d15 (l : loc) (n : nat) : iProp Σ := (∃ vs, l ↦∗ vs ∗ ⌜length vs = n⌝)%I."}
    st = "Lemma x3_spec (n : nat) (l : loc) (γ γₚ γₘ : gname) (z : Z) : inv x12 (d15 l n γ γₚ γₘ) -∗ {{{ True }}} x3 #l #z {{{ RET #(); True }}}."
    assert resources_outside_triple("x3_spec", st, definitions=defs) == []
    # the same predicate heading the premise is flagged
    bad = "Lemma y (l : loc) (n : nat) : d15 l n -∗ {{{ True }}} x3 #l {{{ RET #(); True }}}."
    assert len(resources_outside_triple("y", bad, definitions=defs)) == 1


T = "{{{ True }}} e #() {{{ RET #(); True }}}."


def test_triple_sentinel_accepts_persistent_iris_shapes() -> None:
    """Shapes a real Iris development states before a triple that ARE persistent."""
    ok = [
        "Lemma a N l : inv N (∃ n : nat, l ↦ #n ∗ own γ (● MaxNat n)) -∗ " + T,   # ↦ inside inv
        "Lemma b N l : inv N (l ↦ #0) -∗ " + T,
        "Lemma c N γ l : cinv N γ (l ↦ #0) -∗ " + T,
        "Lemma d l v : l ↦□ v -∗ " + T,                                            # discarded points-to
        "Lemma e γ k v : k ↪[γ]□ v -∗ " + T,
        "Lemma f l : (□ (∀ i v, l ↦ v -∗ WP f #i {{ _, l ↦ v }})) -∗ " + T,      # wand inside a box
        "Lemma g (a : excl unit) : ⌜a = Excl ()⌝ -∗ " + T,                          # Excl in a pure
        "Lemma h l v : l ↦ v -∗ WP mk #l {{ f, {{{ True }}} f #() {{{ RET #(); True }}} }}.",  # nested triple only
        "Lemma i : ⊢ " + T,
        "Lemma j γ : own γ (◯ MaxNat 3) -∗ " + T,
    ]
    for st in ok:
        assert resources_outside_triple("x", st) == [], st


def test_triple_sentinel_flags_shapes_unusable_before_a_boxed_triple() -> None:
    """Shapes that are genuinely unusable before a □-boxed triple."""
    bad = [
        "Lemma a l v : (∀ n, {{{ True }}} f #n {{{ RET #(); True }}}) -∗ l ↦ v -∗ " + T,   # premise after a triple-shaped premise
        "Lemma b l v : l ↦ v -∗ [[{ True }]] !#l [[{ w, RET w; True }]].",                 # total triple
        "Lemma c γ : ghost_var γ (1/2) 0 -∗ " + T,
        "Lemma d n : £ n -∗ " + T,
        "Lemma e γ : locked γ -∗ " + T,
        "Lemma f l v : l ↦{#1/2} v -∗ " + T,
    ]
    for st in bad:
        assert len(resources_outside_triple("x", st)) == 1, st


def test_triple_sentinel_unfolds_design_predicates() -> None:
    defs = {
        "p16": "Definition p16 (γ : gname) (ws : list val) (Q : iProp Σ) : iProp Σ := (∀ vs, own γ (◯E vs) ={⊤}=∗ Q).",
        "mixed": "Definition mixed (l : loc) (v : val) : iProp Σ := (⌜v = #0⌝ ∗ l ↦ v)%I.",
        "boxed2": "Definition boxed2 (l : loc) (v : val) : iProp Σ := (⌜v = #0⌝ ∗ □ (l ↦□ v))%I.",
        "sp": "Definition sp (γ : gname) (Q : iProp Σ) : iProp Σ := saved_prop_own γ DfracDiscarded Q.",
        "spo": "Definition spo (γ : gname) (Q : iProp Σ) : iProp Σ := saved_prop_own γ (DfracOwn 1) Q.",
        "tok": "Definition tok (l : loc) : iProp Σ := meta_token l ⊤.",
        "is_lock": "Definition is_lock (γ : gname) (lk : val) (R : iProp Σ) : iProp Σ := (∃ l, ⌜lk = #l⌝ ∗ inv N (lock_inv γ l R))%I.",
        "is_lock_pers": "Global Instance is_lock_persistent γ lk R : Persistent (is_lock γ lk R) := _.",
    }
    flagged = ["p16 γ ws Q", "∀ vs, p16 γ vs Q", "mixed l v", "spo γ Q", "tok l"]
    passing = ["boxed2 l v", "sp γ Q", "is_lock γ lk R", "inv N (p16 γ ws Q)"]
    for prem in flagged:
        st = f"Lemma x γ ws Q l v lk R : {prem} -∗ " + T
        assert len(resources_outside_triple("x", st, definitions=defs)) == 1, prem
    for prem in passing:
        st = f"Lemma x γ ws Q l v lk R : {prem} -∗ " + T
        assert resources_outside_triple("x", st, definitions=defs) == [], prem


def test_triple_sentinel_on_mixed_resource_shapes_and_multiline_definitions() -> None:
    ok = [
        'Lemma a N l : inv (N .@ "x") (l ↦ #0) -∗ ' + T,
        "Lemma b N l : inv (nroot .@ \"c\") (l ↦ #0) -∗ " + T,
        "Lemma c N γ l k : inv N γ l k (l ↦ #0) -∗ " + T,
        "Lemma d l v : l ↦{DfracDiscarded} v -∗ " + T,
        "Lemma e γ k v : k ↪[γ]{DfracDiscarded} v -∗ " + T,
        "Lemma f γ n : own γ (●□ n) -∗ " + T,
        "Lemma g l : (□ ∀ v, l ↦ v -∗ P) -∗ " + T,
        "Lemma h γ lk l v : is_lock γ lk (l ↦ v) -∗ " + T,
        "Lemma i : ⊢ " + T,
        'Lemma j l v s : l ↦ v -∗ ⌜s = "{{{"⌝ -∗ WP e {{ v, True }}.',
    ]
    for st in ok:
        assert resources_outside_triple("x", st) == [], st
    bad = [
        "Lemma a l v : l ↦ v ⊢ " + T,
        "Lemma b N γ : inv N I ∗ locked γ -∗ " + T,
        "Lemma c N γ v : inv N I ∗ ghost_var γ (1/2) v -∗ " + T,
        "Lemma d γ n : own γ (● n) -∗ " + T,
        "Lemma e p : na_own p ⊤ -∗ " + T,
        "Lemma f N γ : cinv N γ I -∗ cinv_own γ 1 -∗ " + T,
        "Lemma g γ m : ghost_map_auth γ 1 m -∗ " + T,
        "Lemma h γ P : saved_prop_own γ (DfracOwn 1) P -∗ " + T,
    ]
    for st in bad:
        assert len(resources_outside_triple("x", st)) == 1, st
    defs = {
        "p16": "Definition p16 (γ : gname) (ws : list val) (Q : iProp Σ) : iProp Σ := (∀ vs, own γ (◯E vs) ={⊤}=∗ Q).",
        "is_lock2": "Definition is_lock2 (γ : gname) (lk : val) (R : iProp Σ) : iProp Σ := (∃ l, ⌜lk = #l⌝ ∗ inv N (lock_inv γ l R))%I.",
        "later_inv": "Definition later_inv (l : loc) : iProp Σ := ▷ inv N (l ↦ #0).",
        "nl": "Definition nl (l : loc) : iProp Σ :=\n  inv\n N (l ↦ #0).",
        "boxall": "Definition boxall (γ : gname) : iProp Σ := (∀ x, □ (own γ (◯ x) -∗ True))%I.",
        "tok": "Definition tok (γ : gname) (b : bool) : iProp Σ := (⌜b = true⌝ ∨ own γ (Excl ()))%I.",
        "andp": "Definition andp (l : loc) : iProp Σ := (True ∧ l ↦ #0)%I.",
        "impl": "Definition impl (l : loc) (v : val) : iProp Σ := (⌜v = #0⌝ → l ↦ v)%I.",
        "is_ctr": "Definition is_ctr (γ : gname) (l : loc) (P : iProp Σ) : iProp Σ := inv N (ctr_inv γ l P).",
    }
    for prem in ("p16 γ ws Q", "(∀ vs, p16 γ vs Q)", "tok γ b", "andp l", "impl l v"):
        st = f"Lemma x γ ws Q l v b lk R : {prem} -∗ " + T
        assert len(resources_outside_triple("x", st, definitions=defs)) == 1, prem
    for prem in ("is_lock2 γ lk R", "later_inv l", "nl l", "boxall γ", "is_ctr γ l (l ↦ v)"):
        st = f"Lemma x γ ws Q l v b lk R : {prem} -∗ " + T
        assert resources_outside_triple("x", st, definitions=defs) == [], prem
