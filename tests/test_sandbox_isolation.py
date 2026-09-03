"""What a benchmark worker must not be able to read.

These are the checks that stop a benchmark from measuring recall.  They regressed
once, silently: the repo is bound read-only in full, and the repo holds every *other*
rung of the ladder -- including, for a design rung, the same development with the
design **given**.  Anonymisation renames it; it does not withhold it.
"""

from __future__ import annotations

import subprocess
from pathlib import Path

import pytest

from pcp.orch.runners.sandbox import Sandbox, available

REPO = Path(__file__).resolve().parents[1]
BENCH = REPO / "eval" / "corpus" / "bench"

needs_bwrap = pytest.mark.skipif(not available(), reason="bubblewrap is not installed")


def _sandbox(tmp_path: Path, corpus: Path | None) -> Sandbox:
    return Sandbox.for_benchmark(
        tmp_path,
        repo=REPO,
        reference=(REPO / ".pcp" / "reference" / "rwcas_design"),
        corpus=corpus,
        binaries=["bash", "cat", "ls", "grep", "head"],
    )


def _run(sb: Sandbox, cmd: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        sb.wrap(["bash", "-lc", cmd]), capture_output=True, text=True, timeout=120
    )


def test_the_repo_subtrees_that_carry_answers_are_masked(tmp_path) -> None:
    """Named rather than probed, so the intent survives a refactor of `wrap`."""
    sb = _sandbox(tmp_path, None)
    masked = {Path(p).resolve() for p in sb.masked}
    for subtree in (".git", "eval", "docs", "tests", ".pcp"):
        assert (REPO / subtree).resolve() in masked, f"{subtree} is readable by a worker"


def test_the_corpus_under_test_is_bound_back(tmp_path) -> None:
    corpus = BENCH / "rwcas_design"
    sb = _sandbox(tmp_path, corpus)
    assert corpus.resolve() in {Path(p).resolve() for p in sb.unmasked}


@needs_bwrap
@pytest.mark.skipif(not (BENCH / "rwcas_design").exists(), reason="corpus not built")
def test_a_worker_cannot_reach_any_other_rung(tmp_path) -> None:
    sb = _sandbox(tmp_path, BENCH / "rwcas_design")
    listing = _run(sb, f"ls {BENCH}")
    assert listing.stdout.split() == ["rwcas_design"], listing.stdout
    # ... and its own rung is still there, or the run cannot start.
    own = _run(sb, f"ls {BENCH / 'rwcas_design'}")
    assert "Rwcas.v" in own.stdout


@needs_bwrap
def test_a_worker_cannot_grep_the_repo_for_a_reference_body(tmp_path) -> None:
    """The end-to-end version: the thing that actually went wrong."""
    sb = _sandbox(tmp_path, BENCH / "rwcas_design")
    for needle in ("inv rwcasN (rwcas_inv", "linearize_writes", "prophecy is used by every writer"):
        found = _run(sb, f"grep -rl {needle!r} {REPO} 2>/dev/null | head -3")
        assert not found.stdout.strip(), f"{needle!r} is reachable: {found.stdout}"


@needs_bwrap
def test_a_worker_still_has_what_it_needs(tmp_path) -> None:
    """Isolation that breaks the run is not isolation, it is a broken run."""
    sb = _sandbox(tmp_path, BENCH / "rwcas_design")
    assert "gate" in _run(sb, f"head -1 {REPO / 'pcp' / 'orch' / 'gate.py'}").stdout.lower()


@pytest.mark.skipif(not (BENCH / "rwcas_design" / "bench.json").exists(), reason="corpus not built")
def test_the_corpus_metadata_names_nothing_that_was_scrubbed() -> None:
    """`dropped` used to list the scrubbed declarations by name.

    `requestReg`, `AU_write`, `write_inv`, `registry_inv`, `linearize_writes` -- the
    ghost-state architecture and the helping protocol, named. Scrubbing the
    declarations and then naming them is not scrubbing. The names live in
    `reference.json`, which is masked.
    """
    corpus = BENCH / "rwcas_design"
    blob = "".join(p.read_text(errors="ignore") for p in corpus.rglob("*") if p.is_file())
    for scrubbed in ("requestReg", "AU_write", "AU_read", "write_inv", "registry_inv",
                     "registered", "linearize_writes", "extract_result", "ghost_var",
                     "prophec", "/tmp/bench"):
        assert scrubbed not in blob, f"{scrubbed} is readable in the corpus"


def test_a_worker_can_read_the_development_after_a_design_is_adopted(tmp_path) -> None:
    """Adopting a design moves the development into the masked work root.

    The work root is masked so one worker cannot read another's scratch, and until a
    design is adopted that costs nothing: the development is the corpus file, which
    is bound. `_apply_design` rewrites it under `.pcp/work/<run>/<node>.designed/`,
    and from then on `node.json` names a path that exists only outside the sandbox.
    `pcp check` opens it eagerly, so every worker's check loop died on its first call
    with an unhandled FileNotFoundError -- and the run had already spent half an hour
    on the design by the time it got there.
    """
    import asyncio
    import subprocess
    from dataclasses import dataclass

    from pcp.orch.runners.sandbox import Sandbox, SandboxedRunner, available

    if not available():
        pytest.skip("bwrap is not installed")

    repo = Path(__file__).resolve().parent.parent
    run = tmp_path / "work"
    designed = run / "n.designed"
    designed.mkdir(parents=True)
    (designed / "Dev.v").write_text("(* the adopted design *)\n")
    work = run / "n"
    work.mkdir()
    sibling = run / "other"
    sibling.mkdir()
    (sibling / "scratch.v").write_text("another worker's attempt\n")

    @dataclass
    class Fake:
        argv: list
        name: str = "fake"

        def available(self) -> bool:
            return True

        async def run_node(self, node):
            return subprocess.run(self.argv, capture_output=True, text=True).stdout

    @dataclass
    class Payload:
        workdir: Path
        file: str

    def probe(target: Path) -> str:
        runner = SandboxedRunner(
            inner=Fake(argv=["/bin/sh", "-c", f"cat '{target}' 2>&1"]),
            sandbox_factory=lambda w: Sandbox.for_benchmark(w, repo=repo, provider="claude"),
        )
        return asyncio.run(runner.run_node(Payload(workdir=work, file=str(designed / "Dev.v"))))

    assert "the adopted design" in probe(designed / "Dev.v")
    # ... and binding it back must not open the work root generally.
    assert "another worker" not in probe(sibling / "scratch.v")


def test_a_run_cannot_reach_an_earlier_run_s_answer(tmp_path) -> None:
    """The second arm of an ablation must not be able to read the first arm's work.

    Everything a completed run leaves behind is an answer key: the adopted design
    under `.pcp/work/<run>/`, the proof bodies in `.pcp/graphs/<run>.db`, and the
    recorded transcripts under `.pcp/runs/<run>/`. They live beside the new run's own
    workdir, which *is* bound, so this is one `unmasked` entry away from handing over
    a solved copy of the rung.
    """
    import subprocess
    from dataclasses import replace

    from pcp.orch.runners.sandbox import Sandbox, available

    if not available():
        pytest.skip("bwrap is not installed")

    repo = Path(__file__).resolve().parent.parent
    pcp = repo / ".pcp"
    if not pcp.exists():
        pytest.skip("no .pcp tree on this box")

    work = tmp_path / "work" / "n"
    work.mkdir(parents=True)
    designed = tmp_path / "work" / "n.designed"
    designed.mkdir()
    (designed / "Dev.v").write_text("(* this run *)\n")

    sb = Sandbox.for_benchmark(work, repo=repo, provider="claude")
    sb = replace(sb, unmasked=[*sb.unmasked, designed])

    def visible(path: Path) -> bool:
        out = subprocess.run(
            sb.wrap(["/bin/sh", "-c", f"ls -A '{path}' 2>&1"]),
            capture_output=True, text=True,
        ).stdout.strip()
        return bool(out) and "No such file" not in out

    for leaky in (pcp / "work", pcp / "graphs", pcp / "runs", pcp / "reference"):
        if leaky.exists():
            assert not visible(leaky), f"a previous run is readable at {leaky}"


def test_a_rotated_credential_reaches_a_running_worker(tmp_path) -> None:
    """`--ro-bind <file>` pins an inode; an OAuth refresh replaces the file.

    This is what killed the 2026-09-01 design ladder 20 minutes in and had eaten
    rungs before it.  The host rotates `~/.claude/.credentials.json` by atomic
    rename, which the old access token's revocation accompanies; every worker
    spawned before the rotation kept reading the pinned inode and got
    `401 OAuth access token has been revoked`.  Verified directly: with a file bind
    the sandbox still read the old contents after a rename, with a directory bind it
    read the new ones.
    """
    import os
    from pcp.orch.runners.sandbox import _stage_credentials, sync_credentials

    home = tmp_path / "home"
    (home / ".prov").mkdir(parents=True)
    cred = home / ".prov" / "auth.json"
    cred.write_text("OLD", encoding="utf-8")

    pairs = _stage_credentials([".prov/auth.json"], home)
    assert pairs, "a credential in a subdirectory must be staged"
    host_dir, stage = pairs[0]
    assert host_dir == home / ".prov"
    assert (stage / "auth.json").read_text() == "OLD"

    tmp = home / ".prov" / "auth.new"
    tmp.write_text("NEW", encoding="utf-8")
    os.replace(tmp, cred)
    sync_credentials()
    assert (stage / "auth.json").read_text() == "NEW", "the stage must follow the rotation"


def test_staging_copies_only_the_allowlisted_credentials(tmp_path) -> None:
    """The stage is bound as a directory, so what is *not* in it is the guarantee.

    Binding `~/.claude` itself would fix rotation too, and would hand every worker
    the session transcripts this sandbox exists to remove -- on a design rung those
    transcripts discuss the reference proof.
    """
    from pcp.orch.runners.sandbox import _stage_credentials

    home = tmp_path / "home"
    (home / ".prov").mkdir(parents=True)
    (home / ".prov" / "auth.json").write_text("token", encoding="utf-8")
    (home / ".prov" / "transcript.jsonl").write_text("spoilers", encoding="utf-8")
    (home / ".prov" / "projects").mkdir()

    _host, stage = _stage_credentials([".prov/auth.json"], home)[0]
    assert sorted(p.name for p in stage.iterdir()) == ["auth.json"]
