"""Projects whose ``_CoqProject`` is not beside the file (pcp-issues 6, 10, 16, 18).

The shape is the smr-verification one: the project file at the root says
``-Q theories foo`` and developments live in ``theories/<sub>/``.  pcp used to take a
file's directory for the project root everywhere -- the trace workspace, the gate's
flags, the project file copied into a packet -- and wrote statements-only twins next
to the source.
"""

from __future__ import annotations

import subprocess
import time
from pathlib import Path

from conftest import needs_petanque, needs_rocq

from pcp.cli.cmd_trace import trace_workspace
from pcp.config.toolchain import resolve
from pcp.orch.gate import Gate
from pcp.rocq.assemble import Development, stubbed_twin, twin_path
from pcp.rocq.project import (
    ORIGIN_MARKER,
    coq_project_flags,
    development_flags,
    portable_project_text,
    project_origin,
    write_portable_project,
)
from pcp.state.session import ProofSession

A_V = "Definition two := 2.\n"
B_V = """From foo.x Require Import a.
Set Default Proof Using "Type".
Lemma aux : two = 2.
Proof. reflexivity. Qed.
Lemma t : two + 0 = 2.
Proof. rewrite <- aux. reflexivity. Qed.
"""
#: The target's own body never terminates: only a twin that stubs it can open it.
SPIN_V = """From foo.x Require Import a.
Ltac loop := loop.
Lemma spin : two = 2.
Proof. loop. Qed.
Lemma later : two = 2.
Proof. reflexivity. Qed.
"""


def _layout(root: Path, *, build: bool = False) -> Path:
    """``root/_CoqProject`` = ``-Q theories foo``; ``theories/x/a.v``; developments in ``theories/sub/``."""
    (root / "theories" / "x").mkdir(parents=True)
    (root / "theories" / "sub").mkdir(parents=True)
    (root / "_CoqProject").write_text("-Q theories foo\n-arg -w -arg -notation-overridden\ntheories/x/a.v\n")
    (root / "theories" / "x" / "a.v").write_text(A_V)
    (root / "theories" / "sub" / "b.v").write_text(B_V)
    (root / "theories" / "sub" / "spin.v").write_text(SPIN_V)
    if build:
        argv = [*resolve(root).compiler_argv(), "-Q", "theories", "foo", "theories/x/a.v"]
        done = subprocess.run(argv, cwd=root, capture_output=True, text=True, timeout=300, check=False)
        assert done.returncode == 0, done.stderr
    return root


# ------------------------------------------------------------------ fast


def test_rocq_project_is_preferred_over_coq_project(tmp_path: Path) -> None:
    (tmp_path / "_CoqProject").write_text("-Q . old\n")
    (tmp_path / "_RocqProject").write_text("-Q . new\n")
    assert coq_project_flags(tmp_path) == ["-Q", ".", "new"]
    (tmp_path / "_CoqProject").unlink()
    (tmp_path / "sub").mkdir()
    assert development_flags(tmp_path / "sub" / "f.v") == ["-Q", ".", "new.sub", "-Q", str(tmp_path.resolve()), "new"]


def test_development_flags_find_the_root_project_and_name_the_development(tmp_path: Path) -> None:
    root = _layout(tmp_path)
    theories = str((root / "theories").resolve())
    flags = development_flags(root / "theories" / "sub" / "b.v")
    # The copy keeps its logical name (foo.sub.b) and every path works from anywhere.
    assert flags == ["-Q", ".", "foo.sub", "-Q", theories, "foo", "-w", "-notation-overridden"]
    # A development at the root is unchanged in meaning; relative paths become absolute.
    assert development_flags(root / "top.v") == ["-Q", theories, "foo", "-w", "-notation-overridden"]
    # The flat layout keeps its `.` exactly as before.
    (root / "flat").mkdir()
    (root / "flat" / "_CoqProject").write_text("-Q . flat\n-I plugins\n")
    assert development_flags(root / "flat" / "f.v") == ["-Q", ".", "flat", "-I", str((root / "flat" / "plugins").resolve())]


def test_a_directory_that_is_not_an_identifier_stays_outside_the_namespace(tmp_path: Path) -> None:
    root = _layout(tmp_path)
    (root / "theories" / "my-dir").mkdir()
    assert development_flags(root / "theories" / "my-dir" / "f.v")[:3] == ["-Q", str((root / "theories").resolve()), "foo"]


def test_the_portable_project_file_compiles_a_copy_anywhere_and_names_its_origin(tmp_path: Path) -> None:
    root = _layout(tmp_path / "proj")
    elsewhere = tmp_path / "work" / "packet"
    elsewhere.mkdir(parents=True)
    written = write_portable_project(root / "theories" / "sub" / "b.v", elsewhere)
    assert written == elsewhere / "_CoqProject"
    text = written.read_text()
    assert text.splitlines()[0] == f"{ORIGIN_MARKER}{root.resolve()}"
    assert f"-Q {(root / 'theories').resolve()} foo" in text and "-Q . foo.sub" in text
    assert "-arg -notation-overridden" in text and "theories/x/a.v" not in text
    # Read back from the copy: the same flags, and the toolchain is looked up at the origin.
    assert development_flags(elsewhere / "b.v") == development_flags(root / "theories" / "sub" / "b.v")
    assert project_origin(elsewhere) == root.resolve()
    # A copy of the copy (a design round over a staged development) keeps the origin.
    again = tmp_path / "work" / "round2"
    again.mkdir()
    write_portable_project(elsewhere / "b.v", again)
    assert project_origin(again) == root.resolve()
    assert portable_project_text(tmp_path / "work" / "nowhere.v") is None


def test_trace_uses_the_project_root_as_workspace(tmp_path: Path) -> None:
    root = _layout(tmp_path)
    b = root / "theories" / "sub" / "b.v"
    assert trace_workspace(b) == root.resolve()
    assert trace_workspace(b, tmp_path / "other") == tmp_path / "other"
    loose = tmp_path.parent / f"{tmp_path.name}-loose"
    loose.mkdir()
    assert trace_workspace(loose / "f.v") == loose.resolve()


def test_the_twin_lives_under_dot_pcp_and_stubs_the_target_too(tmp_path: Path) -> None:
    root = _layout(tmp_path)
    src = root / "theories" / "sub" / "spin.v"
    twin = stubbed_twin(src, target="spin")
    assert twin == twin_path(src) == root.resolve() / ".pcp" / "twins" / "theories" / "sub" / "spin__pcpfast.v"
    assert not (src.parent / "spin__pcpfast.v").exists()
    text = twin.read_text()
    assert "loop." not in text.split("Lemma spin")[1] and text.count("Admitted.") == 2
    assert (root / ".pcp" / "twins" / ".gitignore").read_text().splitlines()[-1] == "*"
    # The twin no longer depends on the lemma opened.
    assert stubbed_twin(src, target="later").read_text() == text


def test_a_twin_goes_when_its_last_session_closes(tmp_path: Path) -> None:
    root = _layout(tmp_path)
    src = root / "theories" / "sub" / "b.v"
    one = ProofSession(None, None, src, "t", stub_prefix=True)
    two = ProofSession(None, None, src, "aux", stub_prefix=True)
    assert one.file == two.file and Path(one.file).exists()
    one.close()
    one.close()  # idempotent: must not release the other session's hold
    assert Path(two.file).exists()
    two.close()
    assert not Path(two.file).exists()
    assert not (root / ".pcp" / "twins" / "theories").exists()
    three = ProofSession(None, None, src, "t", stub_prefix=True)
    path = Path(three.file)
    del three  # a collected session lets go too
    assert not path.exists()


def test_a_packet_carries_the_rewritten_project_file(tmp_path: Path) -> None:
    from pcp.orch.model import Node, node_id
    from pcp.orch.packet import build_packet

    root = _layout(tmp_path / "proj")
    dev = Development(root / "theories" / "sub" / "b.v")
    node = Node(id=node_id("t"), name="t", statement="Lemma t : two + 0 = 2.", statement_status="frozen")
    paths = build_packet(None, node, dev, [], anchor="t", root=tmp_path / "work", attempt_id=1)
    # The worker's MCP server is rooted in the packet and `pcp check` compiles from it.
    assert development_flags(paths.workdir / "b.v") == development_flags(dev.path)
    assert project_origin(paths.workdir) == root.resolve()


# ------------------------------------------------------------------ live


@needs_rocq
def test_the_gate_passes_a_development_below_the_project_root(tmp_path: Path) -> None:
    root = _layout(tmp_path / "proj", build=True)
    dev = Development(root / "theories" / "sub" / "b.v")
    result = Gate(dev).run("t", [], target_body="rewrite <- aux. reflexivity.", stub_prefix=True)
    assert result.ok, result.render()
    assert "foo.sub.b.t" in result.compile_output
    # A staged / packet copy outside the project compiles through its rewritten project file.
    staged = tmp_path / "workroot" / "t.staged"
    staged.mkdir(parents=True)
    (staged / "b.v").write_text(B_V)
    write_portable_project(dev.path, staged)
    copied = Gate(Development(staged / "b.v")).run("t", [], target_body="rewrite <- aux. reflexivity.", stub_prefix=True)
    assert copied.ok, copied.render()


@needs_rocq
@needs_petanque
def test_trace_resolves_the_root_load_path(tmp_path: Path, capsys) -> None:
    from pcp.cli.main import main

    root = _layout(tmp_path / "proj", build=True)
    out = tmp_path / "t.jsonl"
    assert main(["trace", str(root / "theories" / "sub" / "b.v"), "t", "-o", str(out)]) == 0
    captured = capsys.readouterr()
    assert "stopped at" not in captured.err, captured.err
    assert '"finished": true' in out.read_text().splitlines()[0]


@needs_rocq
@needs_petanque
def test_a_twin_under_dot_pcp_resolves_the_project_and_a_diverging_target_opens(tmp_path: Path) -> None:
    from pcp.state.pool import SessionPool

    root = _layout(tmp_path / "proj", build=True)
    pool = SessionPool(root, size=1, start_timeout=60)
    try:
        session = pool.open(root / "theories" / "sub" / "b.v", "t", stub_prefix=True)
        assert ".pcp/twins/theories/sub/" in session.file
        session.start()
        assert session.run("rewrite <- aux.").ok and session.run("reflexivity.").proof_finished
        started = time.monotonic()
        spin = pool.open(root / "theories" / "sub" / "spin.v", "spin", stub_prefix=True)
        spin.start()
        assert time.monotonic() - started < 30
        assert spin.run("reflexivity.").proof_finished
        twins = [Path(session.file), Path(spin.file)]
    finally:
        pool.close()
    assert not any(t.exists() for t in twins)
    assert not list((root / "theories").rglob("*__pcp*"))

