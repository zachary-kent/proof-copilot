"""A ladder rung may be given what this system produced on the rungs below it.

That is a deliberate hole in an isolation design whose whole point was that there
are no holes, so it is bounded three ways and each is a test here: nothing is given
unless `--library` names it, the corpus stays masked regardless, and whatever *is*
given is named in the packet so the trace records what the run had.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from pcp.orch.packet import render_library


def test_nothing_is_given_by_default(tmp_path: Path) -> None:
    from pcp.orch.runners.sandbox import Sandbox

    box = Sandbox.for_benchmark(tmp_path / "w", repo=tmp_path, corpus=tmp_path / "c")
    assert [p for p in box.unmasked if "library" in str(p)] == []


def test_a_named_library_is_bound_after_the_masks(tmp_path: Path) -> None:
    """Order matters: `eval/` is masked, so a bind that came first would be blanked."""
    from pcp.orch.runners.sandbox import Sandbox

    repo = tmp_path / "repo"
    (repo / "eval" / "corpus").mkdir(parents=True)
    lib = tmp_path / "lib"
    lib.mkdir()
    box = Sandbox.for_benchmark(tmp_path / "w", repo=repo, library=[lib])

    assert lib.resolve() in box.unmasked
    argv = box.wrap(["true"])
    mask_at = argv.index(str((repo / "eval").resolve()))
    bind_at = argv.index(str(lib.resolve()))
    assert mask_at < bind_at, "the library must be bound back after the masks, not before"


def test_the_corpus_tree_stays_masked_even_with_a_library(tmp_path: Path) -> None:
    """The library is the *only* new route in; sibling rungs stay unreachable."""
    from pcp.orch.runners.sandbox import Sandbox

    repo = tmp_path / "repo"
    (repo / "eval" / "corpus" / "bench" / "seqlock").mkdir(parents=True)
    lib = tmp_path / "lib"
    lib.mkdir()
    box = Sandbox.for_benchmark(tmp_path / "w", repo=repo, library=[lib])
    assert (repo / "eval").resolve() in [Path(p).resolve() for p in box.masked]


def test_a_missing_library_path_is_refused_rather_than_ignored() -> None:
    from pcp.cli.main import _library

    with pytest.raises(SystemExit):
        _library(["/nonexistent/for/sure"])


# ------------------------------------------------------- and the worker is told

def test_the_packet_names_what_the_run_was_given(tmp_path: Path) -> None:
    from pcp.orch.assemble import Development
    from pcp.orch.graph import Node
    from pcp.orch.packet import build_packet

    lib = tmp_path / "lib"
    lib.mkdir()
    (lib / "README.md").write_text("# rwcas, as this system solved it\n", encoding="utf-8")

    src = tmp_path / "Dev.v"
    src.write_text("Lemma a : True.\nProof.\nAdmitted.\n", encoding="utf-8")
    node = Node(id="a", name="a", statement="Lemma a : True.", parent=None)

    packet = build_packet(None, node, Development(src), [], anchor="a",
                          root=tmp_path / "run", library=[lib])
    task = packet.task.read_text(encoding="utf-8")
    assert "What you may consult" in task
    assert str(lib) in task
    assert "rwcas, as this system solved it" in task


def test_a_run_given_nothing_is_told_nothing(tmp_path: Path) -> None:
    from pcp.orch.assemble import Development
    from pcp.orch.graph import Node
    from pcp.orch.packet import build_packet

    src = tmp_path / "Dev.v"
    src.write_text("Lemma a : True.\nProof.\nAdmitted.\n", encoding="utf-8")
    node = Node(id="a", name="a", statement="Lemma a : True.", parent=None)
    packet = build_packet(None, node, Development(src), [], anchor="a", root=tmp_path / "run")
    assert "What you may consult" not in packet.task.read_text(encoding="utf-8")


def test_the_decomposer_is_told_too(tmp_path: Path) -> None:
    """It is the decomposer that has to invent a design, so it needs this most."""
    from pcp.orch.assemble import Development
    from pcp.orch.decomposer import render_decomposition_task
    from pcp.orch.graph import Node

    src = tmp_path / "Dev.v"
    src.write_text("Lemma a : True.\nProof.\nAdmitted.\n", encoding="utf-8")
    node = Node(id="a", name="a", statement="Lemma a : True.", parent=None)
    text = render_decomposition_task(node, Development(src), library=[tmp_path / "lib"])
    assert "What you may consult" in text
    assert "worked example" in text


def test_the_section_says_example_not_template() -> None:
    text = render_library([Path("/x")])
    assert "not as something to copy" in text


def test_a_default_binding_does_not_claim_to_come_from_a_config_file(tmp_path, monkeypatch) -> None:
    """A provenance line that names a file which does not exist is a lie, not a label."""
    from pcp.cli import main as cli
    from pcp.orch import providers

    monkeypatch.setattr(providers, "DEFAULT_CONFIG", tmp_path / "absent.toml")
    _model, note = cli._model_for("decomposer", "anthropic")
    if note:
        assert "config.toml" not in note
        assert "built-in default" in note


# ---------------------------------------------------------------- the ladder

def _ladder():
    import sys
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "eval"))
    import ladder

    return ladder


@pytest.mark.skipif(not (Path(__file__).resolve().parents[1] / "eval/corpus/bench/cached_wf").exists(),
                    reason="benchmark corpus not built")
def test_the_cached_pair_is_not_rooted_at_the_same_proof() -> None:
    """`cached_wf` and `cached_strong` share `cas_spec` byte for byte.

    Root both at their largest holdout and the second one becomes a copy job as
    soon as the first one's solution is carried forward -- a "solve" that measures
    transfer rather than proving. So the pair must not share a root.
    """
    import json

    # Read the corpus directly: the cached rungs are not on the ladder (they have no
    # design variant -- their held-out results are stated in terms of the ghost state
    # a designer would have to invent), but if they ever return, rooting both at the
    # largest holdout would make the second a copy job the moment the first is carried.
    def sha(rung, name):
        data = json.loads((Path(__file__).resolve().parents[1] /
                           "eval/corpus/bench" / rung / "bench.json").read_text())
        for h in data["holdout"]:
            if h["anonymised"] == name:
                return h["reference_sha256"]
        raise AssertionError(f"{name} is not a holdout of {rung}")

    assert sha("cached_wf", "c130_spec") == sha("cached_strong", "c129_spec"), (
        "the cached pair shares cas_spec byte for byte; that is why they cannot both "
        "be rooted at their largest holdout"
    )
    assert sha("cached_wf", "f112_spec") != sha("cached_strong", "f111_spec")


@pytest.mark.skipif(not (Path(__file__).resolve().parents[1] / "eval/corpus/bench/rwcas").exists(),
                    reason="benchmark corpus not built")
def test_every_rung_root_is_a_lemma_that_is_actually_in_its_file() -> None:
    """The corpus is anonymised; a rung rooted at `write_spec` would find nothing."""
    from pcp.core.vernac import find_block

    for rung in _ladder().LADDER:
        source = rung.file.read_text(encoding="utf-8")
        assert find_block(source, rung.root_lemma) is not None, \
            f"{rung.name}: no `{rung.root_lemma}` in {rung.file.name}"


def test_the_library_refuses_anything_it_did_not_produce(tmp_path: Path) -> None:
    ladder = _ladder()
    lib = tmp_path / "lib"
    lib.mkdir()
    (lib / "Leak.v").write_text("Lemma x : True. Proof. exact I. Qed.\n", encoding="utf-8")
    with pytest.raises(SystemExit):
        ladder._assert_library_is_clean([lib])

    (lib / "Leak.v").write_text("(* Produced by proof-copilot. *)\nLemma x : True.\n", encoding="utf-8")
    ladder._assert_library_is_clean([lib])  # now fine


def test_the_corpus_can_never_be_a_library_path() -> None:
    ladder = _ladder()
    with pytest.raises(SystemExit):
        ladder._assert_library_is_clean([ladder.CORPUS / "seqlock"])


def test_resuming_a_ladder_still_carries_the_rungs_below(tmp_path, monkeypatch, capsys) -> None:
    """`--only seqlock ...` after a repair must not silently run seqlock cold."""
    ladder = _ladder()
    lib = tmp_path / "library"
    (lib / "solved" / "rwcas_design").mkdir(parents=True)
    (lib / "solved" / "rwcas_design" / "M.v").write_text(
        "(* Produced by proof-copilot. *)\n", encoding="utf-8")
    monkeypatch.setattr(ladder, "LIBRARY", lib)
    monkeypatch.setattr(ladder, "RUNS", tmp_path / "runs")
    (tmp_path / "runs").mkdir()

    seen: list[list[Path]] = []
    monkeypatch.setattr(ladder, "run_rung",
                        lambda rung, *, stamp, library, extra, source=None: (
                            seen.append(list(library)) or
                            {"rung": rung.name, "exit": 0, "timed_out": False,
                             "elapsed_s": 0.0, "record": "", "log": "", "published": None,
                             "tail": "", "outage": ""}))
    monkeypatch.setattr("sys.argv", ["ladder.py", "--only", "seqlock_design",
                                 "--skip-preflight"])
    ladder.main()

    assert seen, "the rung never ran"
    assert any(p.name == "rwcas_design" for p in seen[0]), \
        "a resumed ladder dropped the carry from the rungs below it"


def test_the_library_section_lists_files_not_just_the_directory(tmp_path: Path) -> None:
    """The decomposer has Read/Glob/Grep and no Bash; one run lost a turn to `ls -la`."""
    lib = tmp_path / "solved" / "rwcas"
    lib.mkdir(parents=True)
    (lib / "README.md").write_text("# rwcas, as this system solved it\n", encoding="utf-8")
    (lib / "M8f1e46.v").write_text("(* Produced by proof-copilot. *)\n", encoding="utf-8")
    (lib / "_CoqProject").write_text("-Q . bench\n", encoding="utf-8")

    text = render_library([lib])
    assert str(lib / "M8f1e46.v") in text
    assert str(lib / "_CoqProject") in text
    # The README is the blurb, not a file to open.
    assert str(lib / "README.md") not in text
    assert "rwcas, as this system solved it" in text


def test_an_incomplete_solution_is_not_labelled_complete(tmp_path, monkeypatch) -> None:
    """`"COMPLETE" in "INCOMPLETE"` is True; one rung was handed forward as solved."""
    ladder = _ladder()
    monkeypatch.setattr(ladder, "LIBRARY", tmp_path / "library")

    record = tmp_path / "rec" / "run1" / "solution"
    record.mkdir(parents=True)
    (record / "M.v").write_text(
        "(* Produced by proof-copilot.\n   INCOMPLETE: `x` did not integrate.\n *)\n",
        encoding="utf-8")

    class _Rung:
        name = "rwcas"
        root_lemma = "x"

    dest = ladder.publish(_Rung(), tmp_path / "rec")
    assert "(incomplete)" in (dest / "README.md").read_text(encoding="utf-8")

    (record / "M.v").write_text(
        "(* Produced by proof-copilot.\n   COMPLETE: `x` Qeds.\n *)\n", encoding="utf-8")
    dest = ladder.publish(_Rung(), tmp_path / "rec")
    assert "(complete)" in (dest / "README.md").read_text(encoding="utf-8")


def test_an_outage_stops_the_ladder_instead_of_consuming_rungs(tmp_path, monkeypatch) -> None:
    """A revoked credential took out two cached rungs in under a minute each."""
    ladder = _ladder()
    monkeypatch.setattr(ladder, "LIBRARY", tmp_path / "library")
    monkeypatch.setattr(ladder, "RUNS", tmp_path / "runs")
    (tmp_path / "runs").mkdir()

    ran: list[str] = []

    def _fake(rung, *, stamp, library, extra, source=None):
        ran.append(rung.name)
        log = tmp_path / "runs" / f"{rung.name}.log"
        log.write_text("Failed to authenticate. API Error: 401 OAuth access token "
                       "has been revoked.\n", encoding="utf-8")
        return {"rung": rung.name, "exit": 1, "timed_out": False, "elapsed_s": 3.0,
                "record": "", "log": str(log), "published": None, "tail": "",
                "outage": ladder.looks_like_an_outage(log)}

    monkeypatch.setattr(ladder, "run_rung", _fake)
    monkeypatch.setattr("sys.argv", ["ladder.py", "--skip-preflight"])
    ladder.main()

    assert ran == ["rwcas_design"], f"the ladder burned through {ran} during an outage"


def test_a_real_proof_failure_does_not_stop_the_ladder(tmp_path, monkeypatch) -> None:
    ladder = _ladder()
    log = tmp_path / "x.log"
    log.write_text("not integrated: 2 obligation(s) still open: a, b\n", encoding="utf-8")
    assert ladder.looks_like_an_outage(log) == ""


def test_snapshotting_is_off_until_the_sandbox_takes_an_explicit_repo() -> None:
    """A snapshot silently redefines "the repo", and the repo decides what is masked.

    `Sandbox.for_benchmark` derives `repo` from `__file__`; running the orchestrator
    from a copy therefore moves the masking of `.pcp` (the answer key) to the copy.
    That is not a subtlety to leave half-verified in the isolation layer, so the flag
    is opt-in and documented until `repo` is passed explicitly.
    """
    import inspect

    from pcp.cli import main as cli

    assert "parents[2]" in inspect.getsource(cli._maybe_sandbox), (
        "if the repo is now passed explicitly, snapshotting can be turned back on"
    )


def test_every_rung_budget_leaves_room_for_a_revision_round() -> None:
    """A revision only starts once the frontier finishes, so the wall must fit the
    design round plus two rounds of dispatch.

    cached_strong spent 4500 s designing and 5400 s per node inside a 10800 s wall:
    the first round could not finish, so the failure feedback that the whole
    dispatch-fail-revise loop exists to deliver was never delivered once.
    """
    ladder = _ladder()
    for rung in ladder.LADDER:
        needed = rung.decomposer_seconds + 2 * rung.node_seconds
        assert needed <= rung.wall_seconds, (
            f"{rung.name}: {needed}s of budget inside a {rung.wall_seconds}s wall "
            "leaves no room to act on a failure"
        )


def test_preflight_rejects_a_budget_that_cannot_revise(tmp_path, monkeypatch) -> None:
    ladder = _ladder()
    rung = ladder.Rung("rwcas", node_seconds=5400, decomposer_seconds=4500)
    rung.wall_seconds = 3600
    problems = [p for p in ladder.preflight([rung]) if "cannot fit a revision" in p]
    assert problems, "an unrevisable budget must be caught before anything is spent"


def test_the_ladder_runs_only_design_rungs() -> None:
    """The invariant is the task. Running the proof rungs of the same names measures
    tactic work against a handed-over design -- a different experiment, and the one
    that cost a full night before anyone noticed."""
    ladder = _ladder()
    for rung in ladder.LADDER:
        assert rung.name.endswith("_design"), rung.name
        assert rung.is_design_rung, f"{rung.name} has no blank predicates"


def test_preflight_refuses_a_proof_rung(tmp_path) -> None:
    ladder = _ladder()
    proof = ladder.Rung("seqlock", node_seconds=100, decomposer_seconds=100)
    proof.wall_seconds = 10800
    if not proof.dir.exists():
        import pytest

        pytest.skip("proof corpus not built")
    assert any("proof rung" in p for p in ladder.preflight([proof]))
