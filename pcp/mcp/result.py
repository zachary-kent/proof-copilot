"""The one result schema every tool answers in (pcp-issues D3).

An agent chains calls on what a result says, so every result -- success, Rocq
failure, timeout, lost session, bad arguments -- opens with the same block::

    {"ok":    bool,                 did what was asked happen
     "what":  str,                  one line: what happened
     "where": {file, line, column, sentence, step} | null,
     "goal":  [rendered goal, ...] | null,
                                    after the step on success, the goals the failing
                                    sentence was applied to on failure
     "next":  [str, ...],           concrete next calls, most useful first
     ...tool-specific fields}

and a failure adds ``"error"`` (the Rocq text, shaped by ``pcp.rocq.errors.shape_error``
so its cause survives any cut), ``"timed_out": true`` when a wall clock ran out, and
``"lost": true`` when the ``pet`` process behind the session is gone.  The tool
fields that predate the block (``session``, ``state_id``, ``failure``, ``diagnosis``,
``ledger``, ...) are kept as they were; ``goal`` already meant the rendered goals.

:func:`conform` is the safety net under ``_guard``: a tool (or a result section a later
module adds) that forgets part of the block still answers in the schema.
"""

from __future__ import annotations

from typing import Any

#: The fixed block, in the order it is serialised.
BLOCK_KEYS: tuple[str, ...] = ("ok", "what", "where", "goal", "next")
WHERE_KEYS: tuple[str, ...] = ("file", "line", "column", "sentence", "step")
#: Width of the one-line ``what``.
WHAT_CHARS = 200


def one_line(text: str | None, width: int = WHAT_CHARS) -> str:
    """The first non-empty line of ``text``, whitespace-collapsed and cut at ``width``."""
    first = next((ln for ln in (text or "").splitlines() if ln.strip()), "")
    flat = " ".join(first.split())
    return flat if len(flat) <= width else flat[: width - 1].rstrip() + "…"


def where(
    file: str | None = None,
    line: int | None = None,
    column: int | None = None,
    sentence: str | None = None,
    step: int | None = None,
) -> dict[str, Any] | None:
    """A ``where`` block with every key present, or ``None`` when nothing is known."""
    d = {"file": file, "line": line, "column": column, "sentence": sentence, "step": step}
    return d if any(v is not None for v in d.values()) else None


def result(
    ok: bool,
    what: str,
    *,
    where: dict[str, Any] | None = None,
    goal: list[str] | None = None,
    next: list[str] | tuple[str, ...] = (),  # noqa: A002 -- the schema's own name
    **fields: Any,
) -> dict[str, Any]:
    """A result: the fixed block first, then the tool's own fields."""
    out: dict[str, Any] = {"ok": bool(ok), "what": one_line(what), "where": where, "goal": goal,
                           "next": [n for n in next if n]}
    out.update(fields)  # the block keys are parameters: a field cannot shadow them
    return out


def failure(what: str, error: str | None, **kw: Any) -> dict[str, Any]:
    """``result(ok=False, ...)`` with the ``error`` field every failure carries."""
    return result(False, what, error=error, **kw)


def conform(out: dict[str, Any]) -> dict[str, Any]:
    """``out`` with the fixed block filled in and first; its own values win.

    ``ok`` defaults to "no ``error``" and ``what`` to the error's first line, so a
    tool's bare ``{"error": ...}`` still reads as a failure in the schema.
    """
    if not isinstance(out, dict):
        return result(True, "done", value=out)
    error = out.get("error")
    ok = out.get("ok")
    if ok is None:
        ok = not error
    what = out.get("what") or (one_line(error) if error else ("done" if ok else "failed"))
    block = {"ok": bool(ok), "what": one_line(what), "where": out.get("where"), "goal": out.get("goal"),
             "next": list(out.get("next") or [])}
    rest = {k: v for k, v in out.items() if k not in BLOCK_KEYS}
    return {**block, **rest}
