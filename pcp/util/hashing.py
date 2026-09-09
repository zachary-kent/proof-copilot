"""Content hashes.  One function, several prefixes, so a hash says what it hashes.

Prefixes: ``s:`` statement, ``b:`` blob, ``c:`` closure, ``h:`` hypothesis prop,
``p:`` pure hypothesis, ``e:`` expression, ``g:`` goal.
"""

from __future__ import annotations

import hashlib
import json
from typing import Any


def content_hash(text: str, *, prefix: str = "b:", size: int = 16) -> str:
    return prefix + hashlib.blake2b(text.encode("utf-8"), digest_size=size).hexdigest()


def short_hash(text: str, *, prefix: str = "", size: int = 8) -> str:
    """A shorter hash for display ids.  Never used as a merge key."""
    return prefix + hashlib.blake2b(text.encode("utf-8"), digest_size=size).hexdigest()


def stable_json_hash(data: Any, *, prefix: str = "j:") -> str:
    return content_hash(json.dumps(data, sort_keys=True, ensure_ascii=False, default=str), prefix=prefix)
