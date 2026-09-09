"""The reflected dump against real Rocq: it is the primary path and agrees with the printer."""

from __future__ import annotations

import os
from pathlib import Path

import pytest
from conftest import needs_petanque, needs_rocq

from pcp.state.ipm.reflect import REQUIRE, Reflector, build_idump, env_with_idump
from pcp.state.pool import SessionPool
from pcp.state.trace import Tracer

pytestmark = [needs_petanque, needs_rocq]


@pytest.fixture(scope="module")
def idump_root(tmp_path_factory) -> Path:
    root = tmp_path_factory.mktemp("coq")
    vo = build_idump(root)
    assert vo.exists() and vo == root / "pcp" / "IDump.vo"
    stamp = (root / "pcp" / "IDump.stamp").read_text()
    assert build_idump(root) == vo and (root / "pcp" / "IDump.stamp").read_text() == stamp  # cached
    return root


@pytest.fixture(scope="module")
def reflect_pool(idump_root: Path):
    from conftest import SCRATCH

    env = env_with_idump(dict(os.environ), idump_root)
    assert str(idump_root) in env["ROCQPATH"] and str(idump_root) in env["COQPATH"]
    pool = SessionPool(SCRATCH, size=1, env=env)
    yield pool
    pool.close()


def test_reflected_dump_equals_the_printer_parse(reflect_pool, scratch_dir: Path) -> None:
    plain = reflect_pool.open(scratch_dir / "Blame.v", "persistent_is_not_consumed", pre_commands=REQUIRE)
    dumped = reflect_pool.open(scratch_dir / "Blame.v", "persistent_is_not_consumed", pre_commands=REQUIRE)
    printer = Tracer(plain)
    reflected = Tracer(dumped, reflector=Reflector(dumped))
    printer.start()
    reflected.start()
    for tactic in ['iIntros "[#HP HQ]".', 'iFrame "HP".']:
        p = printer.step(tactic)
        r = reflected.step(tactic)
        assert p.ok and r.ok, (p.error, r.error)
        pg, rg = p.goals[0], r.goals[0]
        assert [(h.id, h.prop, h.klass) for h in pg.ipm_hyps] == [(h.id, h.prop, h.klass) for h in rg.ipm_hyps]
        assert pg.goal == rg.goal and pg.goal_hash == rg.goal_hash and rg.is_ipm
        assert [h.id for h in rg.pure] == [h.id for h in pg.pure]  # the pure context is merged in
        assert rg.raw == pg.raw and p.state_hash == r.state_hash
    assert reflected.reflector is not None and reflected.reflector.available is True
    assert not any(m.startswith("PCP1\t") for m in printer.trace.steps[1].messages)


def test_reflected_dump_names_anonymous_hyps_like_the_printer(reflect_pool, scratch_dir: Path) -> None:
    session = reflect_pool.open(scratch_dir / "Blame.v", "persistent_is_not_consumed", pre_commands=REQUIRE)
    tracer = Tracer(session, reflector=Reflector(session))
    tracer.start()
    step = tracer.step('iIntros "[? ?]".')
    assert step.ok
    goal = step.goals[0]
    assert [h.id for h in goal.spatial] == ["_1", "_2"] and all(h.anonymous for h in goal.spatial)
    assert [h.prop for h in goal.spatial] == ["□ P", "Q"]


def test_one_hypothesis_under_set_printing_all(reflect_pool, scratch_dir: Path) -> None:
    session = reflect_pool.open(scratch_dir / "Basic.v", "load_twice", pre_commands=REQUIRE)
    session.start()
    step = session.run('iIntros "Hl".')
    assert step.ok and step.state is not None
    reflector = Reflector(session)
    assert reflector.probe(state=step.state)
    folded = reflector.dump_hyp("Hl", state=step.state)
    assert folded is not None and folded.name == "Hl" and folded.body == "l ↦ v"
    verbose = reflector.dump_hyp("Hl", state=step.state, printing="Set Printing All.")
    assert verbose is not None and verbose.name == "Hl" and "pointsto" in verbose.body
    assert reflector.dump_hyp("nope", state=step.state) is None
    # The printing option never leaked into the committed state.
    again = reflector.dump_hyp("Hl", state=step.state)
    assert again is not None and again.body == "l ↦ v"
    assert session.history[-1][1] is step.state
    wp = reflector.dump(state=step.state)
    assert wp is not None and wp.goal.startswith("WP") and wp.modality.wp is not None


def test_without_idump_the_printer_parser_is_the_fallback(pool, scratch_dir: Path) -> None:
    session = pool.open(scratch_dir / "Basic.v", "sep_comm")
    tracer = Tracer(session, reflector=Reflector(session))
    tracer.start()
    step = tracer.step('iIntros "[HP HQ]".')
    assert step.ok and [h.id for h in step.goals[0].spatial] == ["HP", "HQ"]
    assert tracer.reflector is not None and tracer.reflector.available is False
