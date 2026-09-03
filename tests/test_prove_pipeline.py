"""The stretch of the pipeline that only exists once a design has been adopted.

Every early benchmark run died at design time -- first on a prompt that leaked the
answer, then on an assembly bug that reordered the design's own definitions, then on
a decomposer deadline. So adoption -> dispatch -> gate -> integration had never
executed at all, and the bugs waiting there were found one live run at a time, at
roughly fifteen minutes and a couple of dollars each. This drives the whole stretch
with canned inputs instead: no models, no money, no network.
"""

from __future__ import annotations

import asyncio
from dataclasses import dataclass, field
from pathlib import Path

import pytest

from tests.conftest import needs_rocq

REPO = Path(__file__).resolve().parent.parent
RUNG = REPO / "eval/corpus/bench/rwcas_design/Rwcas.v"

#: A design that compiles, kept literal rather than regenerated: this is the one a
#: real decomposer round produced, and the point is that the *pipeline* accepts a
#: real design, not that a fixture round-trips.
DESIGN = """{
  "rationale": "helping protocol over a ghost_map registry of write slots",
  "definitions": [
    {"name": "", "text": "From iris.base_logic.lib Require Import ghost_var ghost_map saved_prop."},
    {"name": "rwcasG", "text": "Class rwcasG \\u03a3 := {\\n  rwcas_heapGS :: heapGS \\u03a3;\\n  rwcas_ghost_varG :: ghost_varG \\u03a3 Z;\\n  rwcas_ghost_mapG :: ghost_mapG \\u03a3 gname Z;\\n  rwcas_savedPropG :: savedPropG \\u03a3;\\n}."},
    {"name": "value", "text": "Definition value (\\u03b3 : gname) (n : Z) : iProp \\u03a3 := ghost_var \\u03b3 (1/2)%Qp n."},
    {"name": "write_au", "text": "Definition write_au (\\u03b3 : gname) (q : Z) (\\u03a8 : iProp \\u03a3) : iProp \\u03a3 :=\\n  (AU <{ \\u2203\\u2203 n : Z, value \\u03b3 n }> @ \\u22a4 \\u2216 \\u2191N, \\u2205 <{ value \\u03b3 q, COMM \\u03a8 }>)%I."},
    {"name": "write_done", "text": "Definition write_done (i : gname) : iProp \\u03a3 :=\\n  (\\u2203 \\u03a8 : iProp \\u03a3, saved_prop_own i DfracDiscarded \\u03a8 \\u2217 \\u03a8)%I."},
    {"name": "write_slot", "text": "Definition write_slot (\\u03b3 i : gname) (n0 n : Z) : iProp \\u03a3 :=\\n  ((\\u231cn0 = n\\u231d \\u2217 \\u2203 (q : Z) (\\u03a8 : iProp \\u03a3), saved_prop_own i DfracDiscarded \\u03a8 \\u2217 write_au \\u03b3 q \\u03a8)\\n   \\u2228 write_done i)%I."},
    {"name": "rwcas_inv", "text": "Definition rwcas_inv (\\u03b3\\u1d63 : gname) (l : loc) (\\u03b3 : gname) : iProp \\u03a3 :=\\n  (\\u2203 (n : Z) (M : gmap gname Z),\\n     l \\u21a6 #n \\u2217 ghost_var \\u03b3 (1/2)%Qp n \\u2217 ghost_map_auth \\u03b3\\u1d63 1 M \\u2217\\n     ([\\u2217 map] i \\u21a6 n0 \\u2208 M, write_slot \\u03b3 i n0 n))%I."},
    {"name": "is_rwcas", "text": "Definition is_rwcas (\\u03b3 : gname) (v : val) : iProp \\u03a3 :=\\n  (\\u2203 (l : loc) (\\u03b3\\u1d63 : gname), \\u231cv = #l\\u231d \\u2217 inv rwcasN (rwcas_inv \\u03b3\\u1d63 l \\u03b3))%I."}
  ],
  "children": [
    {"name": "write_slot_register",
     "statement": "Lemma write_slot_register (\\u03b3 \\u03b3\\u1d63 : gname) (n q : Z) (\\u03a8 : iProp \\u03a3) : True.",
     "rationale": "install a pending write in the registry"}
  ],
  "glue_rationale": "the parent registers, then collects"
}"""


@dataclass
class ScriptedDecomposer:
    name: str = "scripted-decomposer"

    def available(self) -> bool:
        return True

    async def run_node(self, node):
        from pcp.orch.runners.base import NodeResult

        return NodeResult(status="qed", raw=DESIGN,
                          trace={"final_text": DESIGN, "model": "scripted"})


@dataclass
class ScriptedProver:
    name: str = "scripted-prover"
    seen: list = field(default_factory=list)

    def available(self) -> bool:
        return True

    async def run_node(self, node):
        from pcp.orch.runners.base import NodeResult

        self.seen.append(node.name)
        # Well-formed but not a proof: exercises the gate without ever faking a QED.
        return NodeResult(status="qed", proof="Proof. iIntros. Admitted.",
                          trace={"final_text": "", "model": "scripted"})


@needs_rocq
@pytest.mark.skipif(not RUNG.exists(), reason="rwcas_design rung not built")
def test_a_design_is_adopted_and_its_obligations_dispatched(tmp_path) -> None:
    from pcp.orch.prove import ProveConfig, prove

    prover = ScriptedProver()
    cfg = ProveConfig(
        file=RUNG, target="write_spec",
        graph_path=tmp_path / "g.db", workroot=tmp_path / "work",
        corpus="rwcas_design", node_seconds=60, max_attempts=1, max_design_rounds=1,
        decomposer_runner=ScriptedDecomposer(), decomposer_seconds=60,
    )
    res = asyncio.run(prove(cfg, runner=prover))

    # The design was adopted: the development moved under the work root.
    designed = tmp_path / "work" / "write_spec.designed" / "Rwcas.v"
    assert designed.exists(), "the adopted design was never written"
    text = designed.read_text()
    # ... with the additions ordered against each other, not as listed.
    for earlier, later in (("write_au", "write_slot"), ("write_done", "write_slot"),
                           ("write_slot", "rwcas_inv")):
        assert text.index(f"Definition {earlier}") < text.index(f"Definition {later}")

    # The root and the stated obligation both reached a prover.
    assert "write_spec" in prover.seen
    assert "write_slot_register" in prover.seen

    # Every packet names the *adopted* development -- the path a sandboxed worker
    # must be able to open, and the one that was masked.
    import json

    for meta in (tmp_path / "work").glob("*/pcp-node.json"):
        assert json.loads(meta.read_text())["file"] == str(designed.resolve())

    # And the gate refused every one of them.
    assert not res.integrated
    assert "still open" in res.integration_detail

    # A run that did not finish still hands its work forward -- labelled, so the
    # next rung cannot read an `Admitted` as a result.
    assert res.solution is None, "no recorder was configured, so nothing to export"


@needs_rocq
@pytest.mark.skipif(not RUNG.exists(), reason="rwcas_design rung not built")
def test_the_run_exports_what_it_produced_for_the_next_rung(tmp_path) -> None:
    """The ladder passes forward what *this system* proved, never the corpus."""
    from pcp.orch.prove import ProveConfig, prove

    cfg = ProveConfig(
        file=RUNG, target="write_spec",
        graph_path=tmp_path / "g.db", workroot=tmp_path / "work",
        record_root=tmp_path / "rec",
        corpus="rwcas_design", node_seconds=60, max_attempts=1, max_design_rounds=1,
        decomposer_runner=ScriptedDecomposer(), decomposer_seconds=60,
    )
    res = asyncio.run(prove(cfg, runner=ScriptedProver()))

    assert res.solution is not None and res.solution.exists()
    text = res.solution.read_text()
    assert text.startswith("(* Produced by proof-copilot.")
    assert "INCOMPLETE" in text, "an unfinished run must say so at the top of the file"
    assert (res.solution.parent / "_CoqProject").exists()


def test_the_header_names_specifications_left_admitted() -> None:
    """A proved root does not make the file complete.

    `seqlock_design` integrated -- `x34_spec` Qed'd with a clean `Print Assumptions`
    -- while `bd31_spec` and `fc32_spec`, two of the three specifications the corpus
    held out, were still `Admitted` in the very same file.  The header said
    "COMPLETE / open: nothing", because both lists are built from the run's graph and
    a spec this run never took as an obligation appears in neither.  That file is
    then handed to the next rung as a worked example, so an axiom got advertised as a
    result.
    """
    from pcp.orch.prove import _solution_header

    class _Root:
        name = "x34_spec"

    header = _solution_header(_Root(), True, ["x34_spec"], [], ["bd31_spec", "fc32_spec"])
    assert "COMPLETE" not in header, "a file with admitted specifications is not complete"
    assert "PARTIAL" in header
    assert "bd31_spec" in header and "fc32_spec" in header

    clean = _solution_header(_Root(), True, ["x34_spec"], [], [])
    assert "COMPLETE" in clean and "PARTIAL" not in clean
    assert "ADMITTED (unproved) in this file: nothing" in clean

    # The root itself being admitted is already reported as `open`; saying it twice
    # would make an unintegrated run look like it had a second, separate problem.
    unintegrated = _solution_header(_Root(), False, [], ["x34_spec"], ["x34_spec"])
    assert "INCOMPLETE" in unintegrated
    assert "ADMITTED (unproved) in this file: nothing" in unintegrated
