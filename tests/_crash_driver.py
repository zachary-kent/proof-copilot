"""Run ``prove()`` on the canary and die with ``os._exit`` at a chosen phase.

Used by ``tests/test_resume.py`` as a subprocess: a real process death runs
no ``finally`` blocks, checkpoints no WAL and releases the run lock only through the
kernel -- what an in-process ``BaseException`` cannot simulate.

usage: _crash_driver.py PHASE WORKDIR CANARY_DIR
PHASE: after_start | after_finish | mid_design
"""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pcp.orch import graph as graph_mod  # noqa: E402
from pcp.orch.contract import DesignContract  # noqa: E402
from pcp.orch.model import Budget  # noqa: E402
from pcp.orch.protocol import NodeResult  # noqa: E402
from pcp.orch.prove import ProveConfig, run  # noqa: E402
from pcp.orch.runners.mock import MockRunner  # noqa: E402

ANSWERS = {
    "canary_swap": 'iIntros "[HA HB]". iFrame.',
    "canary_assoc": 'iIntros "[HA [HB HC]]". iFrame.',
    "canary_main": 'iIntros "H". iDestruct (canary_swap with "H") as "[HQR HP]". iDestruct "HQR" as "[HQ HR]". iFrame.',
    "canary_dup_intro": 'iIntros "[H1 H2]". rewrite /canary_dup. iFrame.',
}
DESIGN = json.dumps({
    "definitions": [{"name": "canary_dup", "text": "Definition canary_dup (P : PROP) : PROP := (P ∗ P)%I."}],
    "children": [
        {"name": "canary_dup_intro", "statement": "Lemma canary_dup_intro (P : PROP) : P ∗ P -∗ canary_dup P."},
        {"name": "canary_swap", "statement": "Lemma canary_swap (A B : PROP) : A ∗ B -∗ B ∗ A."},
    ],
})
EXIT_CODE = 3


class ScriptedDecomposer:
    name = "scripted"

    def available(self) -> bool:
        return True

    async def run_node(self, node):
        return NodeResult(status="qed", raw=DESIGN, trace={"final_text": DESIGN, "model": "scripted"})


def config(phase: str, work: Path, canary: Path) -> ProveConfig:
    kw: dict = {}
    if phase == "mid_design":
        kw = dict(decomposer_runner=ScriptedDecomposer(), decomposer_seconds=5, contract=DesignContract(allow_additions=True))
    return ProveConfig(
        file=canary / "Canary.v", target="canary_main", plan=None if phase == "mid_design" else canary / "plan.v",
        graph_path=work / "graph.db", workroot=work / "work", node_seconds=120, budget=Budget(requests=50, seconds=1800),
        record_root=work / "rec", **kw,
    )


def main() -> int:
    phase, work, canary = sys.argv[1], Path(sys.argv[2]), Path(sys.argv[3])
    runner = MockRunner(answers=dict(ANSWERS))
    if phase == "after_start":
        def die(p) -> None:
            if p.name == "canary_main":
                os._exit(EXIT_CODE)

        runner.on_dispatch = die
    elif phase == "after_finish":
        orig = graph_mod.Graph.finish_attempt

        def finish(self, attempt_id, **kw):
            orig(self, attempt_id, **kw)
            if self.attempt(attempt_id)["node"] == "canary_main" and kw.get("status") == "qed":
                os._exit(EXIT_CODE)

        graph_mod.Graph.finish_attempt = finish  # type: ignore[method-assign]
    elif phase == "mid_design":
        orig_meta = graph_mod.Graph.set_meta

        def set_meta(self, key, value):
            orig_meta(self, key, value)
            if key == "designed_file":
                os._exit(EXIT_CODE)

        graph_mod.Graph.set_meta = set_meta  # type: ignore[method-assign]
    else:
        raise SystemExit(f"unknown phase {phase}")
    result = run(config(phase, work, canary), runner)
    print("finished without dying:", result.render())
    return 0


if __name__ == "__main__":
    sys.exit(main())
