"""The printer parser, the dump reader, the Timeout rule and the trace artifact -- offline.

Every scenario here is a v1 bug named in ``bugs-state-petanque.md``; the test name says
which.  Nothing needs Rocq: the inputs are the exact strings petanque returned (kept
verbatim from the verified experiments).
"""

from __future__ import annotations

import os
from pathlib import Path

import pytest

from pcp.errors import StateError
from pcp.state.ipm.model import IrisGoal, Step, scan_modality
from pcp.state.ipm.parse import goals_from_petanque, looks_like_ipm, parse_coq_hyp_block, parse_goal
from pcp.state.ipm.reflect import clean_body, goal_from_dump, parse_dump
from pcp.state.petanque import PetProcess, StateHandle, coq_timeout, pet_wrapper, wrap_timeout
from pcp.state.session import _single_tactic
from pcp.state.trace import Trace

BOTH = (
    '"Hinv" : inv N P\n'
    "--------------------------------------□\n"
    '"HP" : ▷ P\n'
    '"Hclose" : ▷ P ={⊤ ∖ ↑N,⊤}=∗ emp\n'
    "--------------------------------------∗\n"
    "|={⊤ ∖ ↑N,⊤}=> True"
)
SPATIAL_ONLY = '"Hl" : l ↦ v\n--------------------------------------∗\nWP ! #l;; ! #l {{ w, ⌜w = v⌝ ∗ l ↦ v }}'
INTUIT_ONLY = '"HP" : P\n--------------------------------------□\nP ∗ P ∗ Q'
ANON = (
    "_ : steps_lb n\n"
    "--------------------------------------□\n"
    '"H" : l ↦ #(i1 + i2)\n'
    '"HΦ" : l ↦ #(i1 + i2) ∗ £ (S n) -∗ Φ #i1\n'
    "_ : £ (S n)\n"
    "--------------------------------------∗\n"
    "Φ #i1"
)


def test_all_four_separator_shapes() -> None:
    both = parse_goal(BOTH)
    assert both.is_ipm and [h.id for h in both.intuitionistic] == ["Hinv"]
    assert [h.id for h in both.spatial] == ["HP", "Hclose"]
    assert both.goal == "|={⊤ ∖ ↑N,⊤}=> True" and both.modality.fupd and both.modality.mask == "⊤ ∖ ↑N ⇝ ⊤"
    assert both.intuitionistic[0].persistent is True and both.spatial[0].persistent is None
    sp = parse_goal(SPATIAL_ONLY)
    assert sp.intuitionistic == [] and [h.id for h in sp.spatial] == ["Hl"] and sp.modality.wp is not None
    it = parse_goal(INTUIT_ONLY)
    assert [h.id for h in it.intuitionistic] == ["HP"] and it.spatial == [] and it.goal == "P ∗ P ∗ Q"
    plain = parse_goal("P ∗ Q -∗ Q ∗ P", [(["P", "Q"], "iProp Σ")])
    assert not plain.is_ipm and plain.goal == "P ∗ Q -∗ Q ∗ P" and plain.ipm_hyps == []
    assert plain.pure[0].names == ["P", "Q"] and plain.pure[0].id == "P" and plain.pure[0].klass == "pure"
    assert both.raw == BOTH
    assert looks_like_ipm(BOTH) and not looks_like_ipm("P ∗ Q")


def test_anonymous_hypotheses_are_not_dropped_or_glued() -> None:
    """v1 required a leading quote: `_ : P` vanished or became a continuation line."""
    g = parse_goal(ANON)
    assert [h.id for h in g.intuitionistic] == ["_1"]
    assert g.intuitionistic[0].anonymous and g.intuitionistic[0].prop == "steps_lb n"
    assert [h.id for h in g.spatial] == ["H", "HΦ", "_2"]
    assert g.spatial[1].prop == "l ↦ #(i1 + i2) ∗ £ (S n) -∗ Φ #i1"
    assert g.spatial[2].prop == "£ (S n)" and g.spatial[2].anonymous
    assert g.by_id("_1") is g.intuitionistic[0] and g.by_id("_2") is g.spatial[2]
    d = g.to_json()
    assert d["spatial"][2]["anonymous"] is True and "anonymous" not in d["spatial"][0]
    assert IrisGoal.from_json(d).spatial[2].anonymous


def test_multi_line_props_join_with_layout_stripped() -> None:
    ty = (
        '"IH" : mcounter l n -∗\n'
        "       ▷ (mcounter l (S n) -∗ Φ #()) -∗ WP incr #l {{ v, Φ v }}\n"
        "_ : inv N (mcounter_inv γ l)\n"
        "--------------------------------------□\n"
        '"Hγf" : own γ (◯ MaxNat n)\n'
        "--------------------------------------∗\n"
        "WP if: Snd (#c', #false)%V then #() else incr #l\n  {{ v, Φ v }}"
    )
    g = parse_goal(ty)
    assert [h.id for h in g.intuitionistic] == ["IH", "_1"]
    assert [h.id for h in g.spatial] == ["Hγf"]
    assert g.intuitionistic[0].prop.splitlines()[1].startswith("       ▷")
    assert g.goal.endswith("{{ v, Φ v }}") and "\n" in g.goal


def test_tac_lemma_statements_are_not_contexts() -> None:
    """Iris's own proof-mode lemmas print `Γp---------□` glued inside a statement."""
    ty = "envs_entails (Envs Γp Γs n) Q →\nΓp---------□\nΓs---------∗\nQ ⊢ R"
    g = parse_goal(ty)
    assert not g.is_ipm and g.ipm_hyps == [] and g.goal == ty
    assert not parse_goal("□ (P1 -∗ P2) ∗ of_envs Δ1 ∗ (□ P2 -∗ of_envs Δ2') ⊢ Q").is_ipm


def test_goals_from_petanque_accepts_objects_dicts_and_pairs() -> None:
    class H:
        def __init__(self, names, ty):
            self.names, self.ty = names, ty

    class G:
        def __init__(self, ty, hyps):
            self.ty, self.hyps = ty, hyps

    goals = goals_from_petanque([G(SPATIAL_ONLY, [H(["l"], "loc"), H(["ns", "nt"], "nat")]), G("P", [])])
    assert [g.goal_id for g in goals] == ["g0", "g1"]
    assert [h.id for h in goals[0].pure] == ["l", "ns"] and goals[0].pure[1].names == ["ns", "nt"]
    assert parse_goal("P", [{"names": ["x"], "ty": "nat"}]).pure[0].id == "x"
    assert parse_goal("P", [(["x"], "nat")]).pure[0].prop == "nat"


def test_full_render_coq_context_in_both_shapes_and_unicode_names() -> None:
    """v1 searched the `====` line only in the □ block and required ASCII names."""
    star = parse_goal('x : nat\nσ : state Λ\n====\n"H" : P\n---∗\nQ')
    assert [h.id for h in star.pure] == ["x", "σ"] and [h.id for h in star.spatial] == ["H"]
    box = parse_goal('γ : gname\n====\n"H" : P\n---□\nQ')
    assert [h.id for h in box.pure] == ["γ"] and [h.id for h in box.intuitionistic] == ["H"]
    entries = parse_coq_hyp_block(["x : nat", "σ : state Λ", "Φ : val → iProp Σ", "y := 1 : nat"])
    assert [(e.names, e.prop) for e in entries] == [(["x"], "nat"), (["σ"], "state Λ"), (["Φ"], "val → iProp Σ"), (["y"], "nat")]


def test_modality_is_read_at_the_head_only() -> None:
    assert not scan_modality("P -∗ |={⊤}=> Q").fupd
    assert not scan_modality("P ∗ |==> Q").bupd
    m = scan_modality("WP e @ NotStuck; ⊤ ∖ ↑N {{ Φ }}")
    assert m.mask == "⊤ ∖ ↑N" and m.wp is not None and not m.wp.total
    assert scan_modality("WP e @ s; E [{ v, Φ v }]").wp.total  # type: ignore[union-attr]
    assert scan_modality("▷?q ▷ P").laters == 2 and scan_modality("▷^n P").laters == 1
    assert scan_modality("⌜wp = 1⌝").wp is None


# ------------------------------------------------------------------- reflect


DUMP = [
    'PCP1\tintuitionistic\t(INamed "HP")\tP',
    'PCP1\tspatial\t(INamed "Hl")\t(l ↦ v)%I',
    'PCP1\tspatial\t(INamed "Hclose")\t(▷ P ={⊤ ∖ ↑N,⊤}=∗ emp)%I',
    "PCP1\tspatial\t(IAnon 1)\t(□ P)%I",
    "PCP1\tspatial\t(IAnon 2)\tQ",
    'PCP1\tintuitionistic\t(INamed "Hinv")\t(inv N P)',
    "PCP1\tgoal\t-\t(P ∗ P ∗ Q)%I",
]


def test_dump_records_match_the_printer_parse() -> None:
    goal = goal_from_dump(parse_dump(DUMP))
    assert goal is not None and goal.is_ipm
    assert [h.id for h in goal.intuitionistic] == ["HP", "Hinv"]
    assert [h.id for h in goal.spatial] == ["Hl", "Hclose", "_1", "_2"]
    assert goal.spatial[0].prop == "l ↦ v" and goal.spatial[1].prop == "▷ P ={⊤ ∖ ↑N,⊤}=∗ emp"
    assert goal.spatial[2].prop == "□ P" and goal.spatial[2].anonymous
    assert goal.intuitionistic[1].prop == "inv N P" and goal.goal == "P ∗ P ∗ Q" and goal.goal_hash
    printed = parse_goal('"Hinv" : inv N P\n---□\n"Hl" : l ↦ v\n---∗\nP ∗ P ∗ Q')
    assert goal.goal_hash == printed.goal_hash and goal.spatial[0].hash == printed.spatial[0].hash
    coq = goal_from_dump(parse_dump(["PCP1\tcoq-goal\t-\t(P ∗ Q -∗ Q ∗ P)"]))
    assert coq is not None and not coq.is_ipm and coq.goal == "P ∗ Q -∗ Q ∗ P"
    assert goal_from_dump(parse_dump(["PCP1\tunknown-envs\t-\t?", "PCP1\tgoal\t-\tP"])) is None
    assert goal_from_dump([]) is None
    missing = parse_dump(['PCP1\tmissing\t(INamed "nope")\tTrue'])
    assert missing[0].klass == "missing" and missing[0].body == "True"


def test_scope_wrapper_is_stripped_only_when_it_encloses_the_whole_body() -> None:
    assert clean_body("(A)%I ∗ (B)%I") == "(A)%I ∗ (B)%I"
    assert clean_body("(P ∗ Q)%I") == "P ∗ Q"
    assert clean_body("(inv N P)") == "inv N P"
    assert clean_body("(WP ! #l;; ! #l {{ w, ⌜w = v⌝ ∗ l ↦ v }})%I") == "WP ! #l;; ! #l {{ w, ⌜w = v⌝ ∗ l ↦ v }}"
    assert clean_body("P") == "P"
    assert clean_body("(∃ x,\n   P x)%I") == "∃ x,\n   P x"


# ------------------------------------------------------------------ petanque


def test_timeout_wrapper_rule() -> None:
    """Integer `Timeout` on every dotted sentence; never before a bullet or a brace."""
    assert coq_timeout(0.2) == 1 and coq_timeout(2.5) == 3 and coq_timeout(None) is None
    assert wrap_timeout('iIntros "[HP HQ]".', 5) == ('Timeout 5 iIntros "[HP HQ]".', 1)
    assert wrap_timeout("all: iFrame.", 5) == ("Timeout 5 all: iFrame.", 1)
    assert wrap_timeout("-", 5) == ("-", 0)
    assert wrap_timeout("{", 5) == ("{", 0)
    assert wrap_timeout("2: {", 5) == ("2: {", 0)
    assert wrap_timeout("}", 5) == ("}", 0)
    assert wrap_timeout("- iFrame.", 5) == ("- Timeout 5 iFrame.", 1)
    assert wrap_timeout('Set Printing All. iDumpHyp "HQ".', 7) == ('Timeout 7 Set Printing All. Timeout 7 iDumpHyp "HQ".', 2)
    assert wrap_timeout("Timeout 3 idtac.", 5) == ("Timeout 3 idtac.", 0)
    assert wrap_timeout("(* c *) idtac.", 5) == ("Timeout 5 idtac.", 1)
    assert _single_tactic("iFrame.") == "iFrame" and _single_tactic('iIntros "H".') == 'iIntros "H"'
    assert _single_tactic("2: iFrame.") is None and _single_tactic("idtac. idtac.") is None
    assert _single_tactic("-") is None


def test_wrapper_script_is_atomic_per_uid_and_has_no_pdeathsig(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("TMPDIR", str(tmp_path))
    import tempfile

    tempfile.tempdir = None
    try:
        fake = tmp_path / "pet"
        fake.write_text("#!/bin/sh\nexit 0\n")
        fake.chmod(0o755)
        wrapper = pet_wrapper(str(fake), 1234)
        text = wrapper.read_text()
        assert wrapper.parent.name == f"pcp-pet-{os.getuid()}-1234"
        assert "ulimit -v 1263616" in text and text.endswith('"$@"\n') and text.index("ulimit") < text.index("exec ")
        assert "pdeathsig" not in text and "setpriv" not in text
        assert os.access(wrapper, os.X_OK)
        assert not [p for p in wrapper.parent.iterdir() if p.name.startswith(".")]  # no temp file left behind
        assert pet_wrapper(str(fake), 1234) == wrapper
    finally:
        tempfile.tempdir = None


def test_state_handles_never_cross_processes_or_generations() -> None:
    proc = PetProcess("/tmp", mode="stdio")
    other = PetProcess("/tmp", mode="stdio")
    foreign = StateHandle(process=other.id, generation=0, st=3)
    with pytest.raises(StateError, match="never cross processes"):
        proc.check_handle(foreign)
    stale = StateHandle(process=proc.id, generation=proc.generation - 1, st=3)
    with pytest.raises(StateError, match="restarted"):
        proc.check_handle(stale)
    proc.check_handle(StateHandle(process=proc.id, generation=proc.generation, st=3))
    with pytest.raises(StateError, match="not running"):
        proc.call("goals", StateHandle(process=proc.id, generation=0, st=1))


# --------------------------------------------------------------------- trace


def _goal(spatial: list[tuple[str, str]], goal: str) -> IrisGoal:
    return parse_goal("\n".join(f'"{n}" : {p}' for n, p in spatial) + "\n---∗\n" + goal)


def test_trace_jsonl_round_trip_matches_the_contract(tmp_path: Path) -> None:
    g0 = _goal([("H", "P ∗ Q")], "Q ∗ P")
    g1 = _goal([("HP", "P"), ("HQ", "Q")], "Q ∗ P")
    trace = Trace(file="/x/Basic.v", thm="sep_comm", petanque_file="/x/Basic__pcpfast.v")
    for g in (g0, g1):
        trace.store.update(g)
    trace.steps.append(Step(step=0, state_id=1, tactic="<start>", goals=[g0], state_hash=11, messages=["warn"]))
    trace.steps.append(Step(step=1, state_id=2, tactic='iIntros "[HP HQ]".', goals=[g1], parent_goal="g0", state_hash=22, elapsed_ms=4))
    trace.steps.append(Step(step=2, state_id=-1, tactic="exact I.", goals=[g1], ok=False, error="Coq: no", elapsed_ms=1))
    trace.steps.append(Step(step=3, state_id=3, tactic="idtac.", goals=[g1], parent_goal="g0", state_hash=22, loop_of=1))
    trace.tactics = [s.tactic for s in trace.steps]
    trace.error, trace.failed_at = "Coq: no", 2
    trace.events.append({"step": 1, "kind": "Intro", "tactic": 'iIntros "[HP HQ]".', "goal_id": "g0", "hyp": "HP",
                         "sources": ["H"], "targets": ["HP"], "detail": "", "confidence": "certain", "klass": "spatial"})
    path = trace.to_jsonl(tmp_path / "t.jsonl")
    lines = path.read_text(encoding="utf-8").splitlines()
    import json

    head = json.loads(lines[0])
    assert head["rec"] == "header" and head["v"] == 1 and head["file"] == "/x/Basic.v" and head["failed_at"] == 2
    assert head["petanque_file"] == "/x/Basic__pcpfast.v" and set(head["props"]) >= {g1.spatial[0].hash, g1.goal_hash}
    step1 = json.loads(lines[2])
    assert step1["rec"] == "step" and step1["state_id"] == 2 and step1["parent_goal"] == "g0"
    assert step1["goals"][0]["spatial"][0]["klass"] == "spatial" and step1["goals"][0]["goal"]["prop"] == "Q ∗ P"
    assert json.loads(lines[3])["state_id"] == -1 and json.loads(lines[3])["ok"] is False
    assert json.loads(lines[4])["loop_of"] == 1
    assert json.loads(lines[5])["rec"] == "event" and json.loads(lines[5])["kind"] == "Intro"
    again = Trace.from_jsonl(path)
    assert [s.tactic for s in again.steps] == trace.tactics and again.tactics == trace.tactics
    assert again.failed_at == 2 and again.error == "Coq: no" and again.petanque_file == trace.petanque_file
    assert again.step_at(3).loop_of == 1 and again.step_at(2).goals[0].spatial[1].id == "HQ"  # type: ignore[union-attr]
    assert again.store.to_json() == trace.store.to_json()
    assert len(again.events) == 1 and (again.events[0].to_json() if hasattr(again.events[0], "to_json") else again.events[0])["hyp"] == "HP"
    assert again.live_spatial() == ["HP", "HQ"] and again.dumps() == trace.dumps()


def test_trace_reader_tolerates_legacy_lines_without_rec() -> None:
    text = (
        '{"v": 1, "file": "/f.v", "thm": "t", "props": {}}\n'
        '{"step": 0, "state_id": 1, "tactic": "<start>", "goals": []}\n'
        '{"step": 1, "kind": "Intro", "tactic": "x.", "goal_id": "g0", "hyp": "H", "sources": [], "targets": [], "detail": "", "confidence": "certain", "klass": "spatial"}\n'
    )
    trace = Trace.loads(text)
    assert len(trace.steps) == 1 and len(trace.events) == 1
    with pytest.raises(ValueError):
        Trace.loads('{"step": 0, "state_id": 1, "tactic": "x"}\n')
