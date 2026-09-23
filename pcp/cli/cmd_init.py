"""``pcp init``: make a directory a pcp project (``.pcp/config.toml``).

Writes the example config (:data:`pcp.config.load.EXAMPLE_CONFIG`, the one ``pcp
models --example`` prints) and ``.pcp/.gitignore``, which ignores everything under
``.pcp/`` but the config -- the graph, every worker's attempt directory and a benchmark's
answer key do not belong in a commit; the config does.  Never overwrites a config
without ``--force``.
"""

from __future__ import annotations

import argparse
from pathlib import Path

from pcp.cli.common import absolute
from pcp.config.load import DEFAULT_CONFIG, EXAMPLE_CONFIG, load
from pcp.errors import UsageError
from pcp.util.io import atomic_write_text, ensure_dir

#: ``.pcp/.gitignore``: ignore the run state (graph, attempt directories, answer keys),
#: keep the config -- it is per project and meant to be committed (credentials never live
#: in it: :func:`pcp.config.load.load` rejects them).
INNER_IGNORE = "# proof-copilot run state; the config is committed\n*\n!.gitignore\n!config.toml\n"
_IGNORE_EQUIVALENTS = {".pcp", ".pcp/", "/.pcp", "/.pcp/", ".pcp/*", "/.pcp/*"}


def git_work_tree(start: Path) -> Path | None:
    """The enclosing git work tree (``.git`` directory or worktree file), if any."""
    for candidate in (start, *start.parents):
        if (candidate / ".git").exists():
            return candidate
    return None


def ensure_ignored(pcp_dir: Path) -> bool:
    """Write ``<project>/.pcp/.gitignore`` unless one exists; ``True`` if written."""
    ignore = pcp_dir / ".gitignore"
    if ignore.exists():
        return False
    atomic_write_text(ignore, INNER_IGNORE, follow_symlinks=True, keep_mode=True)
    return True


def config_hidden_by(project: Path) -> Path | None:
    """A project ``.gitignore`` that ignores ``.pcp/`` wholesale (so the config is untracked)."""
    ignore = project / ".gitignore"
    if not ignore.exists():
        return None
    lines = {line.strip() for line in ignore.read_text(encoding="utf-8").splitlines()}
    return ignore if lines & _IGNORE_EQUIVALENTS else None


def cmd_init(args: argparse.Namespace) -> int:
    project = absolute(args.dir) or Path.cwd().resolve()
    if not project.is_dir():
        raise UsageError(f"{project}: not a directory")
    config = project / DEFAULT_CONFIG
    if config.exists() and not args.force:
        raise UsageError(f"{config} already exists; pass --force to overwrite it")
    ensure_dir(config.parent)
    # A committed, user-facing file: preserve a symlink (dotfiles) and don't force 0600.
    atomic_write_text(config, EXAMPLE_CONFIG, follow_symlinks=True, keep_mode=True)
    load(config)  # what we wrote must be what `pcp prove` accepts
    print(f"wrote {config}")
    if ensure_ignored(config.parent):
        print(f"wrote {config.parent / '.gitignore'} (run state ignored, config.toml tracked)")
    if git_work_tree(project) is not None and (hidden := config_hidden_by(project)) is not None:
        print(f"note: {hidden} ignores .pcp/ entirely, so config.toml will not be tracked")
    print(
        "next: edit the [tiers] to the models you have (`pcp models` shows what resolves), "
        "`pcp setup` for the Rocq/Iris toolchain, then `pcp doctor`."
    )
    return 0
