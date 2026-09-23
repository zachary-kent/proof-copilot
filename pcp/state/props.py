"""Propositions as text: evar-aware normalisation and content hashing (PLAN.md 3.2, 4.1).

Iris proofs are evar-dense.  Instantiating an evar reprints every hypothesis that
mentions it, so hashes are computed **modulo evar names**: ``?Φ``, ``?γ``, ``?x0`` and
``?Goal12`` all normalise to the same placeholder.  Evar names may be unicode
(``?Φ`` is the commonest one in Iris); an ASCII-only pattern misses exactly those.
"""

from __future__ import annotations

import re

from pcp.util.hashing import content_hash

#: An evar: ``?`` followed by an identifier (unicode letters allowed), optionally
#: with a numeric suffix.  ``?[x]`` and ``?[?x]`` are the bracketed forms.
_EVAR = re.compile(r"\?\[?\??([^\W\d][\w']*)\]?")
_EVAR_PLACEHOLDER = "?_"


def normalize_evars(prop: str) -> str:
    return _EVAR.sub(_EVAR_PLACEHOLDER, prop)


def normalize_prop(prop: str) -> str:
    """Whitespace-collapsed, evar-normalised text: the hashing key."""
    return " ".join(normalize_evars(prop).split())


def prop_hash(prop: str, *, prefix: str = "h") -> str:
    """A 128-bit content hash of the normalised prop, ``<prefix>:<hex>``.

    Long enough that a collision is not a practical concern for a merge key; the
    render layer shortens it for display only.
    """
    return content_hash(normalize_prop(prop), prefix=prefix + ":")
