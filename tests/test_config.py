"""Configuration: every key that is accepted is read, and secrets are refused."""

from __future__ import annotations

from pathlib import Path

import pytest

from pcp.config import env as penv
from pcp.config.load import EXAMPLE_CONFIG, load
from pcp.config.providers import Binding, default_tiers, describe_bindings, resolve, resolve_effort
from pcp.config.schema import Config, Tiers
from pcp.errors import UsageError


def test_missing_config_yields_detected_defaults(tmp_path: Path) -> None:
    cfg = load(tmp_path / "nope.toml")
    assert cfg.source == "detected defaults"
    assert cfg.flags["recursive_decomposition"] is False


def test_example_config_loads_and_every_key_is_read(tmp_path: Path) -> None:
    p = tmp_path / "config.toml"
    p.write_text("concurrency = 3\naxiom_whitelist = ['Foo.bar']\n" + EXAMPLE_CONFIG, encoding="utf-8")
    cfg = load(p)
    assert cfg.tiers.prover == ["codex/luna", "anthropic/claude-sonnet-5"]
    assert cfg.effort["decomposer"] == "xhigh"
    assert cfg.concurrency == 3
    assert cfg.axiom_whitelist == ["Foo.bar"]
    assert cfg.flags["recursive_decomposition"] is False
    assert cfg.providers["local"].endpoint == "http://localhost:11434"
    assert cfg.source == str(p)


def test_secret_keys_are_refused(tmp_path: Path) -> None:
    p = tmp_path / "config.toml"
    p.write_text('[providers.anthropic]\napi_key = "sk-1"\n', encoding="utf-8")
    with pytest.raises(UsageError, match="Credentials belong"):
        load(p)


def test_bad_effort_is_refused(tmp_path: Path) -> None:
    p = tmp_path / "config.toml"
    p.write_text('[effort]\nprover = "enormous"\n', encoding="utf-8")
    with pytest.raises(UsageError, match="effort"):
        load(p)


def test_unknown_flag_is_refused(tmp_path: Path) -> None:
    p = tmp_path / "config.toml"
    p.write_text("[flags]\nwarp_drive = true\n", encoding="utf-8")
    with pytest.raises(UsageError, match="unknown flag"):
        load(p)


def test_retired_flag_warns_once_and_is_ignored_not_refused(tmp_path: Path) -> None:
    p = tmp_path / "config.toml"
    p.write_text("[flags]\nvacuity_probes = true\nrecursive_decomposition = true\n", encoding="utf-8")
    with pytest.warns(UserWarning, match="vacuity_probes"):
        cfg = load(p)
    assert "vacuity_probes" not in cfg.flags
    assert cfg.flags["recursive_decomposition"] is True


def test_resolve_honours_provider_preference_order() -> None:
    cfg = Config(tiers=Tiers(prover=["codex/luna", "anthropic/claude-sonnet-5"]))
    assert resolve("prover", cfg) == Binding("prover", "codex", "luna")
    # Restricting to the runner's provider picks the first entry FOR that provider,
    # not the first entry overall (legacy dropped the second entry entirely).
    assert resolve("prover", cfg, provider="anthropic") == Binding("prover", "anthropic", "claude-sonnet-5")
    assert resolve("prover", cfg, provider="google") is None
    assert resolve("auditor", cfg) is None


def test_default_tiers_follow_detected_providers() -> None:
    assert default_tiers([]).prover == []
    t = default_tiers(["anthropic"])
    assert t.prover == ["anthropic/claude-sonnet-5"]
    assert t.decomposer == ["anthropic/claude-fable-5"]
    both = default_tiers(["codex", "anthropic"])
    assert both.prover[0] == "codex/luna"
    assert both.decomposer[0] == "anthropic/claude-fable-5"


def test_effort_defaults_per_role() -> None:
    cfg = Config()
    assert resolve_effort("decomposer", cfg) == "xhigh"
    assert resolve_effort("prover", cfg) == "medium"
    cfg.effort["prover"] = "high"
    assert resolve_effort("prover", cfg) == "high"


def test_describe_bindings_shape() -> None:
    text = describe_bindings(Config(tiers=Tiers(prover=["anthropic/claude-sonnet-5"])))
    assert text.startswith("providers detected:")
    assert "prover      anthropic/claude-sonnet-5" in text
    assert "effort medium" in text


def test_with_library_root_keeps_both_variables(monkeypatch) -> None:
    env = {penv.ROCQPATH: "/a:/b"}
    out = penv.with_library_root(env, Path("/x"))
    assert out[penv.ROCQPATH].split(":") == ["/x", "/a", "/b"]
    assert out[penv.COQPATH].split(":") == ["/x", "/a", "/b"]


def test_pet_mem_limit_default(monkeypatch) -> None:
    monkeypatch.delenv(penv.PET_MEM_LIMIT_MB, raising=False)
    assert penv.pet_mem_limit_mb() == penv.DEFAULT_PET_MEM_LIMIT_MB
    monkeypatch.setenv(penv.PET_MEM_LIMIT_MB, "bogus")
    assert penv.pet_mem_limit_mb() == penv.DEFAULT_PET_MEM_LIMIT_MB
    monkeypatch.setenv(penv.PET_MEM_LIMIT_MB, "1024")
    assert penv.pet_mem_limit_mb() == 1024


# ---------------------------------------------------------------- the pinned switch


def _fake_switch(root: Path, name: str = "pcp", binaries: tuple[str, ...] = ("coqc", "pet")) -> Path:
    prefix = root / name
    (prefix / "bin").mkdir(parents=True)
    (prefix / "lib" / "coq" / "user-contrib" / "iris").mkdir(parents=True)
    for b in binaries:
        exe = prefix / "bin" / b
        exe.write_text("#!/bin/sh\n")
        exe.chmod(0o755)
    return prefix


def test_the_switch_defaults_to_the_pinned_name_and_follows_opamroot(tmp_path: Path, monkeypatch) -> None:
    from pcp.util.assets import toolchain_pins

    monkeypatch.delenv("PCP_OPAM_SWITCH", raising=False)
    monkeypatch.setenv("OPAMROOT", str(tmp_path))
    assert penv.opam_switch() == toolchain_pins()["PCP_DEFAULT_OPAM_SWITCH"] == "pcp"
    assert penv.switch_prefix() is None
    prefix = _fake_switch(tmp_path, "other")
    monkeypatch.setenv("PCP_OPAM_SWITCH", "other")
    assert penv.switch_prefix() == prefix and penv.switch_user_contrib() == prefix / "lib" / "coq" / "user-contrib"
    assert penv.switch_prefix("pcp") is None


def test_binaries_fall_back_to_the_switch_after_path(tmp_path: Path, monkeypatch) -> None:
    """Claude Code / Codex start pcp without a login shell: no `opam env`, no eval."""
    for var in (penv.COQC, penv.PET, penv.PET_SERVER, "PCP_OPAM_SWITCH", penv.ROCQPATH, penv.COQPATH):
        monkeypatch.delenv(var, raising=False)
    monkeypatch.setenv("PATH", str(tmp_path / "empty"))
    monkeypatch.setenv("OPAMROOT", str(tmp_path))
    assert penv.coqc_binary() is None
    prefix = _fake_switch(tmp_path)
    assert penv.coqc_binary() == str(prefix / "bin" / "coqc")
    assert penv.pet_binary() == str(prefix / "bin" / "pet") and penv.pet_server_binary() is None
    assert penv.library_roots() == [prefix / "lib" / "coq" / "user-contrib"]
    assert penv.iris_root() == prefix / "lib" / "coq" / "user-contrib"
    onpath = tmp_path / "mine"
    onpath.mkdir()
    (onpath / "coqc").write_text("#!/bin/sh\n")
    (onpath / "coqc").chmod(0o755)
    monkeypatch.setenv("PATH", str(onpath))
    assert penv.coqc_binary() == str(onpath / "coqc"), "the operator's PATH wins"


def test_a_local_switch_is_found_by_its_directory(tmp_path: Path, monkeypatch) -> None:
    local = tmp_path / "proj"
    _fake_switch(local, "_opam")
    monkeypatch.setenv("PCP_OPAM_SWITCH", str(local))
    assert penv.switch_prefix() == local / "_opam"
