"""What every subcommand shares: error mapping, output helpers, path resolution."""

from __future__ import annotations

import argparse
import sys
from collections.abc import Callable
from pathlib import Path

from pcp.errors import PcpError, UsageError
from pcp.util.paths import resolve_from

Command = Callable[[argparse.Namespace], int]


def err(message: str) -> None:
    print(message, file=sys.stderr)


def note(message: str) -> None:
    """A progress line for the operator (stderr, so ``--json`` stdout stays clean)."""
    print(message, file=sys.stderr, flush=True)


def absolute(path: Path | str | None) -> Path | None:
    """Resolve a CLI path against the invocation directory.  Library code never does this."""
    return None if path is None else resolve_from(path)


def run_command(func: Command, args: argparse.Namespace) -> int:
    """Run one subcommand, mapping the error hierarchy to exit codes and messages."""
    try:
        return int(func(args) or 0)
    except PcpError as exc:
        err(str(exc))
        return exc.exit_code
    except KeyboardInterrupt:
        err("interrupted")
        return 130
    except SystemExit as exc:  # argparse exits this way
        if exc.code in (0, None):
            return 0
        if isinstance(exc.code, int):
            return exc.code
        err(str(exc.code))
        return 1


def read_body_arg(path: Path | None) -> str | None:
    """``-`` reads stdin; a path reads the file; ``None`` -> ``None``."""
    if path is None:
        return None
    if str(path) == "-":
        return sys.stdin.read()
    if not Path(path).is_file():
        raise UsageError(f"{path}: no such body file")
    return Path(path).read_text(encoding="utf-8", errors="replace")
