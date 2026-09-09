"""The scripted runner behind the canary answers the way a real worker does."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from pcp.orch.protocol import ANSWER_FILE, NodePayload
from pcp.orch.runners.mock import WRONG_PROOF, MockRunner


def node(tmp_path: Path, name: str = "foo", attempt: int = 1) -> NodePayload:
    return NodePayload(node_id=name, name=name, statement=f"Lemma {name} : True.", file="Dev.v", workdir=tmp_path / name / f"a{attempt}", attempt=attempt)


async def test_the_mock_writes_answer_json_like_a_worker_would(tmp_path: Path) -> None:
    runner = MockRunner({"foo": "exact I."})
    n = node(tmp_path)
    result = await runner.run_node(n)
    assert result.status == "qed" and result.proof == "exact I."
    written = json.loads((n.workdir / ANSWER_FILE).read_text())
    assert written == {"status": "qed", "proof": "exact I."}
    assert result.cost["requests"] == 1 and result.exit_code == 0
    assert runner.available() and runner.name == "mock"


async def test_fail_first_returns_a_wrong_proof_then_the_right_one(tmp_path: Path) -> None:
    runner = MockRunner({"foo": "exact I."}, fail_first={"foo"})
    first = await runner.run_node(node(tmp_path, attempt=1))
    assert first.status == "qed" and first.proof == WRONG_PROOF
    second = await runner.run_node(node(tmp_path, attempt=2))
    assert second.status == "qed" and second.proof == "exact I."


async def test_an_unscripted_node_is_stuck_and_a_status_override_wins(tmp_path: Path) -> None:
    runner = MockRunner({"foo": "exact I."}, statuses={"bar": "contested"})
    missing = await runner.run_node(node(tmp_path, "baz"))
    assert missing.status == "stuck" and "no scripted answer for baz" in missing.evidence
    contested = await runner.run_node(node(tmp_path, "bar"))
    assert contested.status == "contested" and contested.proof == ""


async def test_raise_for_raises_and_on_dispatch_sees_the_payload(tmp_path: Path) -> None:
    seen: list[str] = []
    runner = MockRunner({"foo": "exact I."}, on_dispatch=lambda n: seen.append(n.name), raise_for={"boom"}, delay_s=0.01)
    await runner.run_node(node(tmp_path))
    assert seen == ["foo"]
    with pytest.raises(RuntimeError, match="scripted crash for boom"):
        await runner.run_node(node(tmp_path, "boom"))
