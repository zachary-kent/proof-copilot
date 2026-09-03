"""Content addressing for statements and closures (PLAN.md 8.3).

A freeze pins the **statement closure**, not the source text: source text can differ
by whitespace and mean the same thing, and -- much worse -- can be identical and mean
something different, because `Section`/`Context` variables are invisible on the lemma
line and an upstream `Definition` can change silently underneath it.

Two levels, and the plan is explicit about which is on the critical path:

* ``statement_hash`` -- normalised source text of the statement sentence.  Cheap,
  exact, and sufficient *because* patches are constrained to proof-body spans, so
  the statement is byte-identical by construction rather than by comparison.
* ``closure_hash`` -- the statement plus the transitive source of everything it
  references in the same development, content-addressed.  This is the opt-in deep
  audit, not the per-return check.
"""

from __future__ import annotations

import hashlib
import re

_WS = re.compile(r"\s+")
_COMMENT = re.compile(r"\(\*.*?\*\)", re.S)


def content_hash(text: str, *, prefix: str = "b") -> str:
    return f"{prefix}:{hashlib.blake2b(text.encode('utf-8'), digest_size=16).hexdigest()}"


def normalize_statement(text: str) -> str:
    """Whitespace- and comment-insensitive form of a statement sentence."""
    return _WS.sub(" ", _COMMENT.sub(" ", text)).strip()


def statement_hash(text: str) -> str:
    return content_hash(normalize_statement(text), prefix="s")


def closure_hash(statement: str, referenced: dict[str, str]) -> str:
    """Hash a statement together with the sources of what it references.

    ``referenced`` maps name -> source text, and is hashed in sorted order so the
    result does not depend on discovery order.
    """
    parts = [normalize_statement(statement)]
    for name in sorted(referenced):
        parts.append(f"{name}={normalize_statement(referenced[name])}")
    return content_hash("\n".join(parts), prefix="c")
