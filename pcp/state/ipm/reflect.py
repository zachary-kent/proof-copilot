"""The reflected dump: build and drive ``IDump.v`` (PLAN.md 3.1, the primary path).

The Ltac2 ``iDump`` matches ``envs_entails (Envs Γp Γs c) Q``, walks both contexts and
prints one ``PCP1<TAB>klass<TAB>name<TAB>prop`` message per entry; petanque returns each
Rocq message as its own feedback entry, so record boundaries survive transport with no
delimiter parsing.  Not layout-dependent, survives Iris version bumps, and can print
*one* hypothesis under ``Set Printing All`` while everything else stays folded.

Wire facts (verified, coq-lsp 0.2.5 / Iris 4.5): names print as ``(INamed "HP")`` or
``(IAnon 2)``; bodies as ``(l ↦ v)%I`` when the head is a notation, ``(inv N P)`` for an
application, ``P`` for a variable; a ``coq-goal`` body prints without ``%I``; an absent
name yields a ``missing`` record with body ``True``; only the focused goal is dumped.

The build goes into ``<root>/pcp/IDump.vo`` and is loaded through ``pre_commands`` with
``Require Import pcp.IDump.`` and a ``ROCQPATH``/``COQPATH`` that contains ``root`` --
the worker's file is never edited.  ``Tracer`` uses this path first and the printer
parser (``parse.py``) as the fallback for a step without ``PCP1`` records.  The source
ships as ``pcp/assets/coq/IDump.v`` (:mod:`pcp.util.assets`), so a wheel has it too.
"""

from __future__ import annotations

import contextlib
import fcntl
from collections.abc import Iterator
from dataclasses import dataclass
from pathlib import Path

from pcp.config import env as penv
from pcp.errors import ToolchainError, UsageError
from pcp.state.ipm.model import Hyp, IrisGoal, scan_modality
from pcp.state.petanque import StateHandle
from pcp.state.session import ProofSession
from pcp.util.assets import idump_path
from pcp.util.hashing import content_hash
from pcp.util.io import atomic_write_text, read_text
from pcp.util.proc import run

MARKER = "PCP1\t"
LOGICAL_ROOT = "pcp"
REQUIRE = "Require Import pcp.IDump."
BUILD_TIMEOUT = 600.0


# ---------------------------------------------------------------------- building


def idump_source() -> Path:
    """The packaged ``IDump.v``; :class:`~pcp.util.assets.MissingAsset` (a
    ``ToolchainError``) on a broken install."""
    return idump_path()


@contextlib.contextmanager
def _build_lock(pkg: Path) -> Iterator[None]:
    with open(pkg / ".build.lock", "a+", encoding="utf-8") as fh:
        fcntl.flock(fh.fileno(), fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(fh.fileno(), fcntl.LOCK_UN)


def build_idump(root: Path) -> Path:
    """Compile ``IDump.v`` into ``<root>/pcp/IDump.vo`` (``root`` absolute, given by the caller).

    The cache key covers the source *and* the compiler's version banner, so a ``.vo``
    built by an older Rocq is never reused; the build runs under a file lock so
    concurrent ``proof_open(reflect=True)`` calls cannot race on the ``.vo``.
    """
    root = Path(root)
    if not root.is_absolute():
        raise UsageError(f"build_idump needs an absolute root, got {root}")
    coqc = penv.coqc_binary()
    if coqc is None:
        raise ToolchainError("no coqc/rocq on PATH or in the pinned switch (run `pcp setup`); the reflected dump is unavailable")
    pkg = root / LOGICAL_ROOT
    pkg.mkdir(parents=True, exist_ok=True)
    source = read_text(idump_source())
    banner = run([coqc, "--version"], timeout=60).stdout.strip()
    key = content_hash(source + "\n" + banner)
    vo, stamp = pkg / "IDump.vo", pkg / "IDump.stamp"
    with _build_lock(pkg):
        if vo.exists() and stamp.exists() and read_text(stamp).strip() == key:
            return vo
        atomic_write_text(pkg / "IDump.v", source)
        done = run([coqc, "-R", str(pkg), LOGICAL_ROOT, "-w", "-notation-overridden", "IDump.v"], cwd=pkg, timeout=BUILD_TIMEOUT)
        if not done.ok or not vo.exists():
            raise ToolchainError(f"failed to build IDump.v: {done.spawn_error or done.output[-2000:]}")
        atomic_write_text(stamp, key + "\n")
    return vo


def env_with_idump(env: dict[str, str], root: Path) -> dict[str, str]:
    """``env`` with ``root`` on both ``ROCQPATH`` and ``COQPATH`` (existing entries kept)."""
    return penv.with_library_root(env, Path(root))


# ----------------------------------------------------------------------- reading


@dataclass
class DumpRecord:
    klass: str
    name: str
    body: str
    anonymous: bool = False


def parse_dump(messages: list[str] | tuple[str, ...]) -> list[DumpRecord]:
    """The ``PCP1`` records among a step's feedback messages, in order."""
    out: list[DumpRecord] = []
    for msg in messages:
        text = msg.strip("\n")
        if not text.startswith(MARKER):
            continue
        parts = text[len(MARKER) :].split("\t", 2)
        if len(parts) != 3:
            continue
        klass, raw_name, body = parts
        name, anonymous = _clean_name(raw_name)
        out.append(DumpRecord(klass=klass.strip(), name=name, body=clean_body(body), anonymous=anonymous))
    return out


def _clean_name(raw: str) -> tuple[str, bool]:
    text = " ".join(raw.split())
    if text.startswith("(INamed"):
        q1 = text.find('"')
        q2 = text.rfind('"')
        if 0 <= q1 < q2:
            return text[q1 + 1 : q2], False
        return text, False  # `Set Printing All` prints a String/Ascii tower; the caller keeps its own name
    if text.startswith("(IAnon"):
        return text[len("(IAnon") : -1].strip(), True
    return text.strip("()"), False


def clean_body(raw: str) -> str:
    """Join a wrapped prop and drop the printer's ``( ... )%I`` scope wrapper.

    Only the *outermost* parentheses go, and only when they enclose the whole body,
    so ``(A)%I ∗ (B)%I`` stays as it is.
    """
    text = "\n".join(line.rstrip() for line in raw.splitlines()).strip()
    if text.endswith("%I") and _outer_parens(text[:-2]):
        return text[1:-3].strip()
    if _outer_parens(text):
        return text[1:-1].strip()
    return text


def _outer_parens(text: str) -> bool:
    if not (text.startswith("(") and text.endswith(")")):
        return False
    depth = 0
    for i, ch in enumerate(text):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0 and i != len(text) - 1:
                return False
    return depth == 0


def goal_from_dump(
    records: list[DumpRecord], *, goal_id: str = "g0", pure: list[Hyp] | None = None, raw: str = ""
) -> IrisGoal | None:
    """Assemble an :class:`IrisGoal` from one state's records; ``None`` if unreliable.

    Anonymous entries get ``_1``, ``_2``, ... across the goal, the printer parser's ids.
    """
    if any(r.klass.startswith("unknown") for r in records):
        return None
    intuit: list[Hyp] = []
    spatial: list[Hyp] = []
    goal_text: str | None = None
    is_ipm = True
    n_anon = 0
    for rec in records:
        if rec.klass in ("intuitionistic", "spatial"):
            if rec.anonymous:
                n_anon += 1
                ident = f"_{n_anon}"
            else:
                ident = rec.name
            hyp = Hyp(
                id=ident,
                prop=rec.body,
                klass=rec.klass,  # type: ignore[arg-type]
                persistent=True if rec.klass == "intuitionistic" else None,
                anonymous=rec.anonymous,
            )
            (intuit if rec.klass == "intuitionistic" else spatial).append(hyp)
        elif rec.klass == "goal":
            goal_text = rec.body
        elif rec.klass == "coq-goal":
            goal_text = rec.body
            is_ipm = False
    if goal_text is None:
        return None
    return IrisGoal(
        goal_id=goal_id,
        pure=list(pure or []),
        intuitionistic=intuit,
        spatial=spatial,
        goal=goal_text,
        modality=scan_modality(goal_text),
        is_ipm=is_ipm,
        raw=raw,
    )


# ----------------------------------------------------------------------- driving


class Reflector:
    """Runs ``iDump`` against a session; probes availability once."""

    def __init__(self, session: ProofSession, *, require: str = REQUIRE) -> None:
        self.session = session
        self.require = require
        self.available: bool | None = None

    def probe(self, *, state: StateHandle) -> bool:
        if self.available is None:
            result = self.session.run("iDump.", from_state=state, commit=False)
            self.available = result.ok and any(m.startswith(MARKER) for m in result.messages)
        return self.available

    def dump(self, *, state: StateHandle, goal_id: str = "g0", pure: list[Hyp] | None = None, raw: str = "") -> IrisGoal | None:
        """The focused goal at ``state``, or ``None`` when the dump cannot be trusted."""
        result = self.session.run("iDump.", from_state=state, commit=False)
        if not result.ok:
            return None
        return goal_from_dump(parse_dump(result.messages), goal_id=goal_id, pure=pure, raw=raw)

    def dump_hyp(self, hyp: str, *, state: StateHandle, printing: str | None = None) -> DumpRecord | None:
        """One hypothesis, optionally under other printing options (``"Set Printing All."``).

        The options run in the same speculative command, so they never leak into the
        committed state.  ``None`` when the hypothesis does not exist (a ``missing``
        record is *not* a hypothesis with body ``True``).
        """
        tactic = f'iDumpHyp "{hyp}".'
        if printing:
            tactic = f"{printing} {tactic}"
        result = self.session.run(tactic, from_state=state, commit=False)
        if not result.ok:
            return None
        records = [r for r in parse_dump(result.messages) if r.klass in ("intuitionistic", "spatial")]
        if not records:
            return None
        record = records[0]
        record.name = hyp  # under `Set Printing All` the ident prints as a String/Ascii tower
        return record

    def goals(self, *, state: StateHandle, printed: list[IrisGoal]) -> list[IrisGoal]:
        """``printed`` with its focused goal replaced by the reflected one when available.

        The dump has no Coq-context records and covers the focused goal only, so the
        pure context and the unfocused goals always come from the printer parse.
        """
        if not printed or not self.probe(state=state):
            return printed
        head = printed[0]
        reflected = self.dump(state=state, goal_id=head.goal_id, pure=head.pure, raw=head.raw)
        if reflected is None:
            return printed
        return [reflected, *printed[1:]]
