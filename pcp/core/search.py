"""Premise retrieval and notation resolution (PLAN.md 7, failure modes #5 and #6).

Retrieval failures are a *tool* problem: the Iris/stdpp corpus is large with
non-obvious naming, and agents hallucinate plausible lemma names.  The fix is to ask
Rocq, at the current proof state, rather than to ask the model to remember.

Deliberately not built: an embedding index.  It is not built unless measured
retrieval failures justify it (PLAN.md 7) -- `Search` evaluated at the goal plus a
source grep is a strong baseline, and an index is a maintenance burden that has to
earn its place in the ablations first.
"""

from __future__ import annotations

import re
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

from pcp.core.session import ProofSession


@dataclass
class Premise:
    name: str
    statement: str = ""
    source: str = "search"

    def render(self, width: int = 100) -> str:
        one = " ".join(self.statement.split())
        if len(one) > width:
            one = one[: width - 1] + "…"
        return f"{self.name}\n    {one}" if one else self.name


@dataclass
class SearchResult:
    premises: list[Premise] = field(default_factory=list)
    queries: list[str] = field(default_factory=list)
    note: str = ""

    def render(self, limit: int = 25) -> str:
        if not self.premises:
            return f"no premises found (tried: {', '.join(self.queries)})" + (f"\n{self.note}" if self.note else "")
        lines = [p.render() for p in self.premises[:limit]]
        if len(self.premises) > limit:
            lines.append(f"… {len(self.premises) - limit} more")
        return "\n".join(lines)


_SEARCH_LINE = re.compile(r"^([A-Za-z_][\w'.]*)\s*:\s*(.*)$")


def premise_search(
    session: ProofSession,
    *,
    pattern: str | None = None,
    query: str | None = None,
    scope: str | None = None,
    limit: int = 40,
) -> SearchResult:
    """`Search` / `SearchPattern` evaluated at the current state.

    ``pattern`` is a term pattern (``_ ↦ _``); ``query`` is a set of head symbols or
    substrings.  ``scope`` narrows to a module prefix (``iris.base_logic``).
    """
    result = SearchResult()
    commands: list[str] = []
    inside = f" inside {scope}" if scope else ""
    if pattern:
        commands.append(f"SearchPattern ({pattern}){inside}.")
        commands.append(f"Search {pattern}{inside}.")
    if query:
        terms = " ".join(_quote(t) for t in query.split())
        commands.append(f"Search {terms}{inside}.")
    for command in commands:
        result.queries.append(command)
        for message in session.query(command):
            result.premises.extend(_parse_search(message))
        if len(result.premises) >= limit:
            break
    result.premises = _dedupe(result.premises)[:limit]
    if not result.premises:
        result.note = (
            "Nothing matched at this state. `Search` only sees what is Required here, "
            "so widen the pattern or grep the sources with grep_sources()."
        )
    return result


def _quote(term: str) -> str:
    if term.startswith('"') or re.fullmatch(r"[A-Za-z_][\w'.]*", term):
        return term
    return f'"{term}"'


def _parse_search(message: str) -> list[Premise]:
    """`Search` prints `name:\\n  statement`, wrapping freely."""
    out: list[Premise] = []
    current: Premise | None = None
    for line in message.splitlines():
        m = _SEARCH_LINE.match(line.rstrip())
        if m and not line.startswith((" ", "\t")):
            if current:
                out.append(current)
            current = Premise(name=m.group(1), statement=m.group(2).strip())
        elif current and line.strip():
            current.statement = (current.statement + " " + line.strip()).strip()
    if current:
        out.append(current)
    return out


def _dedupe(premises: list[Premise]) -> list[Premise]:
    seen: set[str] = set()
    out = []
    for p in premises:
        if p.name not in seen:
            seen.add(p.name)
            out.append(p)
    return out


def state_premises(session: ProofSession, limit: int = 60) -> SearchResult:
    """petanque's own ``premises`` route: everything in scope at this state."""
    result = SearchResult(queries=["petanque/premises"])
    try:
        raw = session.premises()
    except Exception as exc:  # noqa: BLE001 -- retrieval failing is not fatal
        result.note = f"petanque premises unavailable: {exc}"
        return result
    for entry in raw or []:
        if isinstance(entry, dict):
            name = entry.get("name") or entry.get("full_name") or ""
            statement = entry.get("type") or entry.get("statement") or ""
        else:
            name, statement = str(entry), ""
        if name:
            result.premises.append(Premise(name=name, statement=str(statement), source="premises"))
    result.premises = result.premises[:limit]
    return result


def grep_sources(roots: list[Path], pattern: str, *, limit: int = 40) -> SearchResult:
    """Source-grep passthrough, for when `Search` cannot see the module yet."""
    result = SearchResult(queries=[f"grep {pattern!r}"])
    for root in roots:
        if not Path(root).exists():
            continue
        try:
            proc = subprocess.run(
                ["grep", "-rn", "--include=*.v", "-E", pattern, str(root)],
                capture_output=True,
                text=True,
                timeout=60,
            )
        except (FileNotFoundError, subprocess.TimeoutExpired):
            result.note = "grep is unavailable"
            return result
        for line in proc.stdout.splitlines()[:limit]:
            path, _, rest = line.partition(":")
            lineno, _, text = rest.partition(":")
            m = re.search(r"\b(?:Lemma|Theorem|Definition|Instance)\s+([\w']+)", text)
            result.premises.append(
                Premise(name=m.group(1) if m else f"{Path(path).name}:{lineno}", statement=text.strip(), source="grep")
            )
    result.premises = _dedupe(result.premises)[:limit]
    return result


# ---------------------------------------------------------------------- notation

@dataclass
class NotationInfo:
    token: str
    locate: str = ""
    unfolds_to: str = ""
    tactics: list[str] = field(default_factory=list)
    note: str = ""

    def render(self) -> str:
        lines = [f"notation: {self.token}"]
        if self.locate:
            lines.append(self.locate.strip())
        if self.unfolds_to:
            lines.append(f"unfolds to: {self.unfolds_to}")
        if self.tactics:
            lines.append("IPM tactics that apply: " + ", ".join(self.tactics))
        if self.note:
            lines.append(self.note)
        return "\n".join(lines)


#: Which IPM tactics apply to which shape.  Mechanical, and exactly the knowledge an
#: agent is missing when it stares at `={E}=∗` and guesses.
_TACTIC_TABLE: list[tuple[str, list[str]]] = [
    (r"=\{.*\}=∗|=\{.*\}=>", ["iMod", "iApply fupd_mask_weaken", "iModIntro"]),
    (r"\|==>", ["iMod", "iModIntro"]),
    (r"-∗", ["iApply", "iSpecialize", "iIntros"]),
    (r"∗-∗", ["iSplit", "iApply", "iRewrite"]),
    (r"▷", ["iNext", "iModIntro", "iMod"]),
    (r"□", ["iModIntro", "iDestruct ... as \"#H\"", "iIntros \"#H\""]),
    (r"∗", ["iSplitL", "iSplitR", "iFrame", "iDestruct ... as \"[H1 H2]\""]),
    (r"∨", ["iLeft", "iRight", "iDestruct ... as \"[H1|H2]\""]),
    (r"∧", ["iSplit", "iDestruct ... as \"[H1 H2]\""]),
    (r"∃", ["iExists", "iDestruct ... as (x) \"H\""]),
    (r"⌜", ["iPureIntro", "iDestruct ... as %H"]),
    (r"WP|wp", ["wp_apply", "wp_pures", "iApply wp_", "wp_bind"]),
    (r"↦", ["wp_load", "wp_store", "iCombine", "iDestruct (pointsto_agree ...)"]),
]


def notation_resolve(session: ProofSession, token: str) -> NotationInfo:
    """What does `={E}=∗` mean, what does it unfold to, which tactics apply?"""
    info = NotationInfo(token=token)
    for message in session.query(f'Locate Notation "{token}".'):
        info.locate += message + "\n"
    if not info.locate.strip():
        for message in session.query(f'Locate "{token}".'):
            info.locate += message + "\n"
    m = re.search(r":=\s*(.+)", info.locate)
    if m:
        info.unfolds_to = " ".join(m.group(1).split())[:200]
    info.tactics = tactics_for(token)
    if not info.locate.strip():
        info.note = (
            "Rocq did not recognise this as a notation at this state. It may be "
            "project-local, or need its module Required first."
        )
    return info


def tactics_for(text: str) -> list[str]:
    """Offline: the tactic shortlist for a printed shape, no Rocq needed."""
    out: list[str] = []
    for pattern, tactics in _TACTIC_TABLE:
        if re.search(pattern, text):
            for t in tactics:
                if t not in out:
                    out.append(t)
    return out


# ------------------------------------------------------- local documentation index

def library_roots() -> list[Path]:
    """The installed Rocq libraries, which are the authoritative documentation."""
    import os

    roots: list[Path] = []
    for var in ("ROCQPATH", "COQPATH"):
        for entry in (os.environ.get(var) or "").split(":"):
            if entry and Path(entry).exists():
                roots.append(Path(entry))
    guess = Path.home() / ".opam" / "pcp" / "lib" / "coq" / "user-contrib"
    if guess.exists() and guess not in roots:
        roots.append(guess)
    return roots


def build_local_index(roots: list[Path], out: Path, *, libraries: tuple[str, ...] = ("iris", "stdpp")) -> tuple[Path, int]:
    """Extract every declaration from the installed sources into one grep-able file.

    A worker that cannot reach the network still needs to answer "does a lemma
    shaped like this exist, and what is it called?" -- failure mode #6, and the one
    where agents hallucinate most confidently.  The library it is compiling against
    *is* the documentation; this just makes it searchable in one pass instead of
    170 files.

    Format is one record per declaration::

        iris/proofmode/coq_tactics.v:412  Lemma tac_and_destruct : ...

    which greps well for both a name and a shape.
    """
    from pcp.core.vernac import parse_blocks

    out.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with out.open("w", encoding="utf-8") as fh:
        fh.write(
            "# Declarations from the installed Rocq libraries. Search with grep, e.g.\n"
            "#   grep -n 'wp_cmpxchg' index.txt\n"
            "#   grep -nE 'Lemma .*↦.*∗' index.txt\n\n"
        )
        for root in roots:
            for library in libraries:
                base = root / library
                if not base.exists():
                    continue
                for path in sorted(base.rglob("*.v")):
                    try:
                        source = path.read_text(encoding="utf-8")
                    except OSError:
                        continue
                    rel = path.relative_to(root)
                    line_starts = _line_index(source)
                    for block in parse_blocks(source):
                        if block.head not in ("Lemma", "Theorem", "Definition", "Instance", "Corollary"):
                            continue
                        line = _line_of(line_starts, block.statement_start)
                        fh.write(f"{rel}:{line}  {' '.join(block.statement.split())}\n")
                        count += 1
    return out, count


def _line_index(source: str) -> list[int]:
    out = [0]
    for i, ch in enumerate(source):
        if ch == "\n":
            out.append(i + 1)
    return out


def _line_of(starts: list[int], offset: int) -> int:
    import bisect

    return bisect.bisect_right(starts, offset)
