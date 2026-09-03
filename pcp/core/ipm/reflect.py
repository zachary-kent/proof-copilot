"""v2 acquisition path: drive the Ltac2 ``iDump`` and read it back (PLAN.md 3.1).

The open question the plan flags -- *"whether tactic message output is cleanly
capturable through petanque run"* -- is answered yes: petanque returns each Rocq
message as its own entry in ``State.feedback``, so one ``Message.print`` per
hypothesis survives transport with its record boundaries intact and no delimiter
parsing at all.

This path is preferred over ``parse.py`` because it is not layout-dependent, it
survives Iris version bumps, and it can set printing options per hypothesis.  The
printer parser remains as the fallback for states where ``iDump`` cannot run.
"""

from __future__ import annotations

import re
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path

from pcp.core.ipm.model import Hyp, IrisGoal, scan_modality
from pcp.core.session import ProofSession, rocq_binary

MARKER = "PCP1\t"
#: The logical Rocq path the dump library is installed under.
LOGICAL_ROOT = "pcp"


class ReflectUnavailable(RuntimeError):
    """``iDump`` is not loadable in this session -- fall back to the printer parser."""


# ----------------------------------------------------------------------- building

def idump_source() -> Path:
    return Path(__file__).resolve().parents[3] / "coq" / "IDump.v"


def build_idump(out_root: Path) -> Path:
    """Compile ``IDump.v`` into ``out_root/pcp/`` so ``COQPATH`` can find it.

    Rocq treats every ``COQPATH`` entry as a user-contrib root, so a ``.vo`` at
    ``<root>/pcp/IDump.vo`` is importable as ``pcp.IDump`` with no project flags --
    which matters because the file the worker is proving is *theirs*, and pcp must
    not have to edit it to observe it.
    """
    coqc = rocq_binary()
    if coqc is None:
        raise ReflectUnavailable("no coqc/rocq on PATH")
    pkg = out_root / LOGICAL_ROOT
    pkg.mkdir(parents=True, exist_ok=True)
    src = pkg / "IDump.v"
    source_text = idump_source().read_text(encoding="utf-8")
    vo = pkg / "IDump.vo"
    if vo.exists() and src.exists() and src.read_text(encoding="utf-8") == source_text:
        return vo
    src.write_text(source_text, encoding="utf-8")
    proc = subprocess.run(
        [coqc, "-R", str(pkg), LOGICAL_ROOT, "-w", "-notation-overridden", "IDump.v"],
        cwd=str(pkg),
        capture_output=True,
        text=True,
        timeout=600,
    )
    if proc.returncode != 0 or not vo.exists():
        raise ReflectUnavailable(f"failed to build IDump.v: {proc.stdout}\n{proc.stderr}")
    return vo


def coqpath_with(out_root: Path) -> str:
    import os

    existing = os.environ.get("COQPATH", "")
    root = str(out_root)
    parts = [p for p in existing.split(":") if p and p != root]
    return ":".join([root, *parts])


# ------------------------------------------------------------------------ reading

_NAMED = re.compile(r'INamed\s+"([^"]*)"')
_ANON = re.compile(r"IAnon\s+(\S+?)\)?$")
#: `Message.of_constr` prints Iris props in scope-annotated form: `(l ↦ v)%I`.
_SCOPED = re.compile(r"^\((.*)\)%I$", re.S)


@dataclass
class DumpRecord:
    klass: str
    name: str
    body: str


def parse_dump(messages: list[str]) -> list[DumpRecord]:
    """Parse the ``PCP1`` records out of a step's feedback messages."""
    out: list[DumpRecord] = []
    for msg in messages:
        text = msg.strip("\n")
        if not text.startswith(MARKER):
            continue
        parts = text[len(MARKER) :].split("\t", 2)
        if len(parts) != 3:
            continue
        klass, raw_name, body = parts
        out.append(DumpRecord(klass=klass.strip(), name=_clean_name(raw_name), body=_clean_body(body)))
    return out


def _clean_name(raw: str) -> str:
    raw = raw.strip()
    m = _NAMED.search(raw)
    if m:
        return m.group(1)
    m = _ANON.search(raw)
    if m:
        return f"?{m.group(1)}"
    return raw.strip("()")


def _clean_body(raw: str) -> str:
    """Join a wrapped prop and drop the scope annotation the printer adds."""
    text = "\n".join(line.rstrip() for line in raw.splitlines()).strip()
    m = _SCOPED.match(text)
    if m:
        text = m.group(1).strip()
    return text


def goal_from_dump(records: list[DumpRecord], *, goal_id: str = "g0") -> IrisGoal | None:
    """Assemble an :class:`IrisGoal` from the dump records of one state."""
    if not records:
        return None
    goal = IrisGoal(goal_id=goal_id)
    seen_goal = False
    for rec in records:
        if rec.klass == "intuitionistic":
            goal.intuitionistic.append(Hyp(id=rec.name, prop=rec.body, klass="intuitionistic", persistent=True))
        elif rec.klass == "spatial":
            goal.spatial.append(Hyp(id=rec.name, prop=rec.body, klass="spatial"))
        elif rec.klass == "goal":
            goal.goal = rec.body
            seen_goal = True
        elif rec.klass == "coq-goal":
            goal.goal = rec.body
            goal.is_ipm = False
            seen_goal = True
    if not seen_goal:
        return None
    goal.goal_hash = ""
    goal.__post_init__()
    goal.modality = scan_modality(goal.goal)
    return goal


# ------------------------------------------------------------------------- driving

class Reflector:
    """Runs ``iDump`` against a session, with a one-shot availability probe."""

    def __init__(self, session: ProofSession, *, require: str = "Require Import pcp.IDump.") -> None:
        self.session = session
        self.require = require
        self.available: bool | None = None

    def probe(self, state=None) -> bool:
        if self.available is not None:
            return self.available
        result = self.session.run("iDump.", from_state=state, commit=False)
        self.available = result.ok and any(m.startswith(MARKER) for m in result.messages)
        return self.available

    def dump(self, state=None, *, goal_id: str = "g0") -> IrisGoal | None:
        """Dump the focused goal, or ``None`` if the reflected path is unavailable."""
        result = self.session.run("iDump.", from_state=state, commit=False)
        if not result.ok:
            return None
        return goal_from_dump(parse_dump(result.messages), goal_id=goal_id)

    def dump_hyp(self, hyp: str, *, printing: str | None = None, state=None) -> DumpRecord | None:
        """One hypothesis, optionally under different printing options.

        This is the capability the printer parser cannot offer at all: render *one*
        hypothesis with ``Set Printing All`` while everything else stays folded.
        """
        tactic = f'iDumpHyp "{hyp}".'
        if printing:
            tactic = f"{printing} {tactic}"
        result = self.session.run(tactic, from_state=state, commit=False)
        if not result.ok:
            return None
        records = parse_dump(result.messages)
        if not records:
            return None
        # Under `Set Printing All` the ident prints as a raw `String (Ascii …)` tower.
        # The caller asked for this hypothesis by name, so keep the name it used.
        record = records[0]
        record.name = hyp
        return record


def has_idump() -> bool:
    return idump_source().exists() and (rocq_binary() is not None) and shutil.which is not None
