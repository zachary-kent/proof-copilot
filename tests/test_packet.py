"""pcp.orch.packet: fresh attempt directories and the TASK.md contract."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from pcp.orch.model import Node, node_id
from pcp.orch.packet import PLACEHOLDER_BODY, build_packet, default_docs, render_library, render_task
from pcp.rocq.assemble import Development, NodeSpec
from pcp.rocq.decls import find_block

SIBS = [
    NodeSpec("canary_swap", "Lemma canary_swap (A B : PROP) : A ∗ B -∗ B ∗ A."),
    NodeSpec("canary_assoc", "Lemma canary_assoc (A B C : PROP) : A ∗ (B ∗ C) -∗ (A ∗ B) ∗ C.", body='iIntros "[HA [HB HC]]". iFrame.'),
]


def _node(name: str, statement: str, **kw) -> Node:
    return Node(id=node_id(name), name=name, statement=statement, statement_status="frozen", **kw)


@pytest.fixture
def dev(canary_dir) -> Development:
    return Development(canary_dir / "Canary.v")


def _build(dev, tmp_path, node, attempt_id=1, **kw):
    return build_packet(None, node, dev, SIBS, anchor="canary_main", root=tmp_path / "work", attempt_id=attempt_id, **kw)


def test_attempt_dir_is_fresh_per_attempt(dev, tmp_path):
    node = _node("canary_swap", SIBS[0].statement)
    p1 = _build(dev, tmp_path, node, attempt_id=1)
    assert p1.workdir == tmp_path / "work" / node.id / "a1"
    (p1.workdir / "answer.json").write_text('{"status": "stuck"}')
    p2 = _build(dev, tmp_path, node, attempt_id=2)
    assert p2.workdir != p1.workdir and not (p2.workdir / "answer.json").exists()
    # Rebuilding the same attempt wipes what a killed run left behind.
    p1b = _build(dev, tmp_path, node, attempt_id=1)
    assert p1b.workdir == p1.workdir and not (p1.workdir / "answer.json").exists()
    assert {p.name for p in p1.workdir.iterdir()} == {"Canary.v", "_CoqProject", "pcp-node.json", "TASK.md"}


def test_child_packet_has_placeholder_body_and_admitted_anchor(dev, tmp_path):
    node = _node("canary_swap", SIBS[0].statement)
    paths = _build(dev, tmp_path, node)
    text = paths.scratch.read_text()
    own = find_block(text, "canary_swap")
    assert own is not None and own.body(text).strip() == PLACEHOLDER_BODY and own.ender == "Qed"
    assert find_block(text, "canary_main").ender == "Admitted"
    assert find_block(text, "canary_assoc").body(text).strip().startswith("iIntros")


def test_anchor_packet_has_placeholder_in_the_anchor(dev, tmp_path):
    node = _node("canary_main", "Lemma canary_main P Q R : P ∗ Q ∗ R -∗ R ∗ Q ∗ P.", rank="root")
    paths = _build(dev, tmp_path, node)
    text = paths.scratch.read_text()
    assert find_block(text, "canary_main").body(text).strip() == PLACEHOLDER_BODY
    assert find_block(text, "canary_swap").ender == "Admitted"


def test_previous_body_surfaces_in_scratch_and_task(dev, tmp_path):
    node = _node("canary_swap", SIBS[0].statement)
    partial = 'iIntros "[HA HB]".\niSplitL "HB".'
    paths = _build(dev, tmp_path, node, attempt=2, evidence="gate: FAIL", previous_body=partial)
    text = paths.scratch.read_text()
    assert find_block(text, "canary_swap").body(text).strip() == partial
    task = paths.task.read_text()
    section = task.index("## Your previous attempt's proof (partial)")
    assert section > task.index("## What went wrong last time (attempt 1)")
    assert partial in task[section:] and section < task.index("## How to work")
    plain = _build(dev, tmp_path, node, attempt_id=3).task.read_text()
    assert "previous attempt's proof" not in plain


def test_pcp_node_json_contract(dev, tmp_path):
    node = _node("canary_swap", SIBS[0].statement)
    paths = _build(dev, tmp_path, node, attempt=2, attempt_id=5)
    meta = json.loads(paths.node_file.read_text())
    assert set(meta) == {"node", "target", "anchor", "file", "statement", "corpus", "siblings", "attempt", "diagnose", "attempt_id", "scratch", "preamble"}
    assert meta["file"] == str(dev.path.resolve()) and Path(meta["corpus"]).is_absolute()
    assert meta["attempt"] == 2 and meta["attempt_id"] == 5 and meta["scratch"] == "Canary.v" and meta["diagnose"] is False
    by_name = {s["name"]: s["proved"] for s in meta["siblings"]}
    assert by_name == {"canary_swap": False, "canary_assoc": True}


def test_task_sections_in_contract_order(dev, tmp_path):
    node = _node("canary_swap", SIBS[0].statement, intent="because")
    paths = _build(
        dev, tmp_path, node, attempt=2, evidence="boom", premises=["lemma_x"], skills=["# Prover\nbe careful"],
        state_tools=["proof_open", "proof_step"], docs=[("the index", "/abs/index.txt")], library=[tmp_path / "lib"],
        design="## Design brief\nsome design",
    )
    task = paths.task.read_text()
    order = [
        "# Prove `canary_swap`", "## The statement", "## Why this lemma exists", "## Design brief", "## Lemmas you may use",
        "## Premise shortlist", "## What went wrong last time (attempt 1)", "## Documentation", "## What you may consult",
        "## Tools available to you", "## How to work", "## How to answer", "\n---\n\n# Prover",
    ]
    positions = [task.index(h) for h in order]
    assert positions == sorted(positions)
    assert "`canary_swap` (" not in task and "- `canary_assoc` (proved): `Lemma canary_assoc" in task
    assert "- `mcp__pcp__proof_open` — open this lemma" in task and "replays that proof" in task
    assert '"status": "contested"' in task and "Never add a hypothesis" in task and "Canary.v" in task
    assert (paths.workdir / ".mcp.json").exists() and json.loads(paths.node_file.read_text())["diagnose"] is True


def test_no_tools_means_no_diagnosis_paragraph_and_no_mcp_json(dev, tmp_path):
    paths = _build(dev, tmp_path, _node("canary_swap", SIBS[0].statement), docs=[])
    task = paths.task.read_text()
    assert "replays that proof" not in task and "## Documentation" not in task and "## Tools" not in task
    assert not (paths.workdir / ".mcp.json").exists()


def test_packet_is_deterministic(dev, tmp_path):
    node = _node("canary_swap", SIBS[0].statement)
    a = _build(dev, tmp_path, node, docs=[]).task.read_text()
    b = _build(dev, tmp_path, node, docs=[]).task.read_text()
    assert a == b
    assert render_task(node, dev, SIBS, scratch_name="Canary.v", docs=[]) == render_task(node, dev, SIBS, scratch_name="Canary.v", docs=[])


def test_resume_evidence_says_previous_run(dev, tmp_path):
    task = render_task(_node("canary_swap", SIBS[0].statement), dev, SIBS, scratch_name="C.v", evidence="x", attempt=1, docs=[])
    assert "## What went wrong last time (the previous run)" in task


def test_default_docs_requires_an_absolute_index(tmp_path):
    with pytest.raises(ValueError):
        default_docs("relative/index.txt")
    index = tmp_path / "index.txt"
    index.write_text("x")
    labels = [label for label, _ in default_docs(index)]
    assert labels[0] == "every declaration in Iris and std++, one per line"
    assert all(label.startswith("the Iris") for label in labels[1:])
    assert not any(str(index) in p for _l, p in default_docs(tmp_path / "missing.txt"))


def test_render_library_lists_readme_note_and_files(tmp_path):
    lib = tmp_path / "lib"
    lib.mkdir()
    (lib / "README.md").write_text("# The paper\n")
    (lib / "a.v").write_text("")
    (lib / "b.v").write_text("")
    text = render_library([lib])
    assert text.startswith("## What you may consult\n") and f"- `{lib}` — The paper" in text
    assert f"    - `{lib / 'a.v'}`" in text and "README.md" not in text.split("— The paper")[1]


def test_the_packet_tells_workers_to_run_checks_in_the_foreground(tmp_path) -> None:
    """A headless worker ran `pcp check` in the background and ended its turn to wait for
    it, which ended the session (spec-only seqlock_wf resume, 2026-09-05)."""
    from pcp.orch.model import Node, node_id
    from pcp.orch.packet import render_task
    from pcp.rocq.assemble import Development

    src = tmp_path / "D.v"
    src.write_text("Lemma root : True.\nProof.\nAdmitted.\n", encoding="utf-8")
    node = Node(id=node_id("root"), name="root", statement="Lemma root : True.", statement_status="frozen", rank="root")
    text = render_task(node, Development(src), [], scratch_name="D.v")
    assert "FOREGROUND" in text and "ends the session" in text


def test_a_reviewed_node_is_not_told_it_contested() -> None:
    from pcp.orch.packet import render_evidence
    from pcp.orch.protocol import ADJUDICATED_MARKER

    contested = "\n".join(render_evidence(f"{ADJUDICATED_MARKER} use the other lemma\n\nYour contest was: it is false"))
    reviewed = "\n".join(render_evidence(f"{ADJUDICATED_MARKER} use the other lemma\n\nYour last attempt's evidence was: gate: FAIL"))
    assert "Your contest was reviewed" in contested and "never" not in contested
    assert "Your attempts were reviewed" in reviewed and "contest was reviewed" not in reviewed
