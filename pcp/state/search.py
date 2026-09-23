"""Premise retrieval and notation resolution (PLAN.md 7; failure modes #5 and #6).

Retrieval failures are a *tool* problem: the Iris/stdpp corpus is large with
non-obvious naming and agents hallucinate plausible lemma names.  So ask Rocq at the
current proof state, and fall back to the sources.

What Rocq needs, verified against 9.1 (map-source 5.5): ``Search ident`` errors unless
``ident`` is an existing global, while ``Search "str"`` is a substring match on names --
so every query term is sent **quoted**; ``-foo`` negations stay bare; a term pattern is
sent as ``SearchPattern (...)`` (conclusions only) and then ``Search ...`` (hypotheses
too).  ``Locate Notation "..."`` is not a command; ``Locate "..."`` is.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Any

from pcp.errors import PcpError
from pcp.rocq.decls import DECL_HEADS
from pcp.rocq.lexer import identifiers
from pcp.rocq.library import grep_sources
from pcp.state.ipm.skeleton import parse_skeleton

if TYPE_CHECKING:
    from pcp.state.session import ProofSession

DEFAULT_LIMIT = 40
RENDER_LIMIT = 25


@dataclass(frozen=True)
class Hit:
    name: str
    statement: str = ""
    #: ``search`` (Rocq), ``grep`` (sources).
    source: str = "search"

    def render(self, width: int = 110) -> str:
        one = " ".join(self.statement.split())
        if len(one) > width:
            one = one[: width - 1] + "…"
        return f"{self.name}\n    {one}" if one else self.name


@dataclass
class SearchResult:
    answer: str
    count: int
    hits: list[Hit] = field(default_factory=list)
    #: The literal vernacular sentences that were actually run.
    queries: list[str] = field(default_factory=list)
    note: str = ""


# ---------------------------------------------------------------------- quoting

_IDENT_PATH = re.compile(r"[^\W\d][\w'.]*")


def quote_term(term: str) -> str:
    """A ``Search`` term: quoted substring unless it is a negation or already quoted."""
    t = term.strip()
    if not t or t.startswith("-") or (t.startswith('"') and t.endswith('"') and len(t) > 1):
        return t
    return '"' + t.replace('"', '""') + '"'


def _balanced(text: str) -> bool:
    depth = 0
    for ch in text:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
            if depth < 0:
                return False
    return depth == 0


def _inside(scope: str, notes: list[str]) -> str:
    s = " ".join(scope.split())
    if not s:
        return ""
    if all(_IDENT_PATH.fullmatch(part) for part in s.split()):
        return f" inside {s}"
    notes.append(f"scope {scope!r} is not a module path; ignored")
    return ""


# ---------------------------------------------------------------------- parsing

_RECORD = re.compile(r"^([^\s:]+):(?:\s+(.*))?$")


def parse_search_output(message: str) -> list[Hit]:
    """Rocq prints ``Name: statement`` per hit, continuation lines indented."""
    out: list[Hit] = []
    name: str | None = None
    statement = ""
    for line in message.splitlines():
        m = _RECORD.match(line.rstrip())
        if m and not line[:1].isspace():
            if name is not None:
                out.append(Hit(name, statement.strip()))
            name, statement = m.group(1), (m.group(2) or "")
        elif name is not None and line.strip():
            statement += " " + line.strip()
    if name is not None:
        out.append(Hit(name, statement.strip()))
    return out


def _dedupe(hits: list[Hit]) -> list[Hit]:
    seen: set[str] = set()
    out: list[Hit] = []
    for h in hits:
        if h.name not in seen:
            seen.add(h.name)
            out.append(h)
    return out


def _run(session: ProofSession, command: str, notes: list[str]) -> list[str]:
    try:
        return list(session.query(command))
    except PcpError as exc:
        notes.append(f"`{command}` failed: {exc}")
        return []


# ----------------------------------------------------------------------- search


def premise_search(
    session: ProofSession,
    *,
    pattern: str = "",
    query: str = "",
    scope: str = "",
    roots: list[Path] | None = None,
    limit: int = DEFAULT_LIMIT,
) -> SearchResult:
    """``Search`` / ``SearchPattern`` at the current state, then a source grep.

    ``pattern`` is a term pattern (``_ ↦ _``); ``query`` is whitespace-separated name
    substrings (``add_comm``, ``-assoc``); ``scope`` a module path (``inside``).
    ``roots`` are workspace directories to grep before the installed libraries.
    """
    queries: list[str] = []
    notes: list[str] = []
    hits: list[Hit] = []
    inside = _inside(scope, notes)
    p = " ".join(pattern.split())
    if p:
        if not _balanced(p):
            notes.append(f"pattern {p!r} has unbalanced brackets; not sent to Rocq")
        else:
            for command in (f"SearchPattern ({p}){inside}.", f"Search {p}{inside}."):
                queries.append(command)
                for message in _run(session, command, notes):
                    hits.extend(parse_search_output(message))
                if len(_dedupe(hits)) >= limit:
                    break
    terms = [quote_term(t) for t in query.split() if t.strip()]
    if terms:
        command = f"Search {' '.join(terms)}{inside}."
        queries.append(command)
        for message in _run(session, command, notes):
            hits.extend(parse_search_output(message))
    hits = _dedupe(hits)[:limit]
    if not hits and (p or terms):
        hits = _grep(query or p, roots, session, limit, notes)
        queries.append(f"grep {query or p!r}")
    if not hits:
        notes.insert(0, "Nothing matched at this state or in the sources. `Search` only sees what is Required "
                        "here, so widen the pattern or check the module is imported.")
    note = "\n".join(notes)
    return SearchResult(answer=_render(hits, queries, note), count=len(hits), hits=hits, queries=queries, note=note)


def _grep_regex(text: str) -> str:
    tokens = text.split()
    if not tokens:
        return ""
    if len(tokens) == 1 and "_" not in tokens[0]:
        return re.escape(tokens[0])
    return r"\s*".join(r"\S+" if t == "_" else re.escape(t) for t in tokens)


def _grep(text: str, roots: list[Path] | None, session: Any, limit: int, notes: list[str]) -> list[Hit]:
    rx = _grep_regex(text)
    if not rx:
        return []
    dirs = list(roots or [])
    file = getattr(session, "file", None)
    if not dirs and file is not None:
        dirs = [Path(file).parent]
    lines: list[str] = []
    for d in dirs:
        d = Path(d)
        if d.is_dir():
            lines += grep_sources(rx, roots=[d.parent], libraries=(d.name,), limit=limit)
    if len(lines) < limit:
        lines += grep_sources(rx, limit=limit - len(lines))
    hits = [_grep_hit(line) for line in lines]
    if hits:
        notes.append("`Search` found nothing at this state; these are source lines (grep), not premises in scope.")
    return _dedupe(hits)[:limit]


def _grep_hit(line: str) -> Hit:
    path, _, rest = line.partition(":")
    lineno, _, text = rest.partition(":")
    idents = identifiers(text)
    name = idents[1] if len(idents) > 1 and idents[0] in DECL_HEADS else f"{Path(path).name}:{lineno.strip()}"
    return Hit(name, text.strip(), source="grep")


def _render(hits: list[Hit], queries: list[str], note: str) -> str:
    if not hits:
        return f"no premises found (tried: {', '.join(queries)})" + (f"\n{note}" if note else "")
    lines = [h.render() for h in hits[:RENDER_LIMIT]]
    if len(hits) > RENDER_LIMIT:
        lines.append(f"… {len(hits) - RENDER_LIMIT} more")
    if note:
        lines.append(note)
    return "\n".join(lines)


# --------------------------------------------------------------------- notation


@dataclass
class Interpretation:
    notation: str
    term: str
    scope: str = ""
    origin: str = ""


@dataclass
class NotationInfo:
    token: str
    locate: str = ""
    interpretations: list[Interpretation] = field(default_factory=list)
    unfolds_to: str = ""
    definition: str = ""
    tactics: list[str] = field(default_factory=list)
    note: str = ""

    def render(self) -> str:
        lines = [f"notation: {self.token}"]
        for i in self.interpretations[:4]:
            scope = f" : {i.scope}" if i.scope else ""
            origin = f" (from {i.origin})" if i.origin else ""
            lines.append(f'  Notation "{i.notation}" := {i.term}{scope}{origin}')
        if not self.interpretations and self.locate:
            lines.append(self.locate.strip())
        if self.unfolds_to:
            lines.append(f"unfolds to: {self.unfolds_to}")
        if self.definition:
            lines.append(f"definition: {self.definition}")
        if self.tactics:
            lines.append("IPM tactics that apply: " + ", ".join(self.tactics))
        if self.note:
            lines.append(self.note)
        return "\n".join(lines)


_NOTATION_BLOCK = re.compile(r'^Notation\s+"((?:[^"]|"")*)"\s*:=\s*', re.M)
_SCOPE = re.compile(r":\s*([A-Za-z_][\w']*_scope)\b")
_ORIGIN = re.compile(r"\(from\s+([^)]+)\)")


def parse_locate_output(text: str) -> list[Interpretation]:
    """Each ``Notation "..." := (term) ... : scope (from Mod)`` block of ``Locate``."""
    out: list[Interpretation] = []
    matches = list(_NOTATION_BLOCK.finditer(text))
    for i, m in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        block = text[m.end() : end]
        term, rest = _balanced_prefix(block.lstrip())
        out.append(Interpretation(
            notation=m.group(1).replace('""', '"'),
            term=" ".join(term.split()),
            scope=(_SCOPE.search(rest) or [None, ""])[1] or "",
            origin=(_ORIGIN.search(rest) or [None, ""])[1] or "",
        ))
    return out


def _balanced_prefix(text: str) -> tuple[str, str]:
    """The parenthesised term at the start of ``text`` (or its first line), and the rest."""
    if not text.startswith("("):
        head, _, tail = text.partition("\n")
        return head.strip(), tail
    depth = 0
    for i, ch in enumerate(text):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return text[: i + 1], text[i + 1 :]
    return text, ""


def _head_ident(term: str) -> str:
    idents = identifiers(term)
    return idents[0] if idents else ""


def notation_resolve(session: ProofSession, token: str) -> str:
    """What ``={E}=∗`` means, what it unfolds to, which IPM tactics apply."""
    info = notation_info(session, token)
    return info.render()


def notation_info(session: ProofSession, token: str) -> NotationInfo:
    tok = " ".join(token.split())
    info = NotationInfo(token=tok)
    notes: list[str] = []
    if not tok:
        info.note = "no token given"
        return info
    escaped = tok.replace('"', '""')
    info.locate = "\n".join(_run(session, f'Locate "{escaped}".', notes)).strip()
    info.interpretations = parse_locate_output(info.locate)
    if info.interpretations:
        info.unfolds_to = info.interpretations[0].term
        head = _head_ident(info.unfolds_to)
        if head:
            printed = "\n".join(_run(session, f"Print {head}.", notes)).strip()
            if printed:
                one = " ".join(printed.split())
                info.definition = one if len(one) <= 300 else one[:299] + "…"
    info.tactics = tactics_for(tok)
    if not info.locate:
        info.note = ("Rocq did not recognise this as a notation at this state. It may be project-local, "
                     "or need its module Required first.")
    if notes:
        info.note = (info.note + "\n" if info.note else "") + "\n".join(notes)
    return info


# ----------------------------------------------------------------- tactic table

#: Which IPM tactics apply to which connective; order is the display order.
_TACTIC_TABLE: list[tuple[str, list[str]]] = [
    ("fupd_wand", ["iMod", "iApply fupd_mask_weaken", "iModIntro", "iIntros"]),
    ("fupd", ["iMod", "iApply fupd_mask_weaken", "iModIntro"]),
    ("bupd", ["iMod", "iModIntro"]),
    ("wand", ["iApply", "iSpecialize", "iIntros"]),
    ("wand_iff", ["iSplit", "iApply", "iRewrite"]),
    ("later", ["iNext", "iModIntro", "iMod"]),
    ("box", ["iModIntro", 'iDestruct ... as "#H"', 'iIntros "#H"']),
    ("sep", ["iSplitL", "iSplitR", "iFrame", 'iDestruct ... as "[H1 H2]"']),
    ("or", ["iLeft", "iRight", 'iDestruct ... as "[H1|H2]"']),
    ("and", ["iSplit", 'iDestruct ... as "[H1 H2]"']),
    ("exists", ["iExists", 'iDestruct ... as (x) "H"']),
    ("forall", ["iIntros (x)", "iSpecialize ... $! x"]),
    ("pure", ["iPureIntro", "iDestruct ... as %H"]),
    ("wp", ["wp_apply", "wp_pures", "iApply wp_", "wp_bind"]),
    ("pointsto", ["wp_load", "wp_store", "iCombine", "iDestruct (pointsto_agree ...)"]),
]
_KIND_KEY = {
    "sep": "sep", "and": "and", "or": "or", "wand": "wand", "wand_iff": "wand_iff", "exists": "exists",
    "forall": "forall", "pure": "pure", "later": "later", "bupd": "bupd", "fupd": "fupd", "fupd_step": "fupd",
    "box": "box", "intuitionistically": "box", "persistently": "box",
}
_FUPD_WAND = re.compile(r"^=\{[^}]*\}=(?:∗|\*)$|^==∗$")
_FUPD = re.compile(r"^\|=\{[^}]*\}(?:▷)?=>$")


_BRACED = re.compile(r"\{\s*([^{}]*?)\s*\}")


def _token_keys(text: str) -> set[str]:
    keys: set[str] = set()
    depth = 0
    # `Locate` prints notations with spaced braces (`={ E }=∗`); close them up.
    text = _BRACED.sub(lambda m: "{" + m.group(1).replace(" ", "") + "}", text)
    for tok in text.replace("(", " ( ").replace(")", " ) ").split():
        if tok == "(":
            depth += 1
            continue
        if tok == ")":
            depth = max(0, depth - 1)
            continue
        if _FUPD_WAND.match(tok):
            keys.add("fupd_wand")
        elif _FUPD.match(tok):
            keys.add("fupd")
        elif tok == "|==>":
            keys.add("bupd")
        elif tok in ("-∗", "−∗"):
            keys.add("wand")
        elif tok == "∗-∗":
            keys.add("wand_iff")
        elif tok.startswith("▷"):
            keys.add("later")
        elif tok in ("□", "<pers>", "■"):
            keys.add("box")
        elif tok == "∗":
            keys.add("sep")
        elif tok == "∨":
            keys.add("or")
        elif tok == "∧":
            keys.add("and")
        elif tok.startswith("∃"):
            keys.add("exists")
        elif tok.startswith("∀"):
            keys.add("forall")
        elif tok.startswith("⌜"):
            keys.add("pure")
        elif tok in ("WP", "TWP") and depth == 0:
            keys.add("wp")
        elif tok.startswith("↦"):
            keys.add("pointsto")
    return keys


def tactics_for(text: str) -> list[str]:
    """Offline: the IPM tactic shortlist for a printed shape, by *standalone* connective.

    Driven by the skeleton's top connective first, then by space-delimited tokens, so
    the ``∗`` inside ``-∗``, ``∗-∗`` and ``l ↦∗ vs`` never suggests ``iSplitL``.
    """
    if not text.strip():
        return []
    keys = _token_keys(text)
    first = _KIND_KEY.get(getattr(parse_skeleton(text), "kind", ""), "")
    out: list[str] = []
    for key, tactics in _TACTIC_TABLE:
        if key == first or key in keys:
            for t in tactics:
                if t not in out:
                    out.append(t)
    if first and first in dict(_TACTIC_TABLE):
        head = [t for t in dict(_TACTIC_TABLE)[first] if t in out]
        out = head + [t for t in out if t not in head]
    return out
