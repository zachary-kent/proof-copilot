"""Small text helpers used by renders and reports."""

from __future__ import annotations

import textwrap


def one_line(text: str, width: int = 110) -> str:
    one = " ".join(text.split())
    return one if len(one) <= width else one[: width - 1] + "…"


def tail_lines(text: str, n: int) -> str:
    lines = text.strip().splitlines()
    return "\n".join(lines[-n:])


def head_tail(text: str, *, head: int, tail: int) -> str:
    """Keep the first ``head`` and last ``tail`` characters, marking the cut."""
    if len(text) <= head + tail:
        return text
    return text[:head] + f"\n… [{len(text) - head - tail} chars elided] …\n" + text[-tail:]


def clip(text: str, limit: int) -> str:
    return text if len(text) <= limit else text[: limit - 1] + "…"


def indent(text: str, prefix: str = "  ") -> str:
    return textwrap.indent(text, prefix)


def wrap(text: str, width: int = 88) -> str:
    return "\n".join(textwrap.wrap(text, width)) if text else ""


def plural(n: int, word: str, plural_word: str | None = None) -> str:
    return f"{n} {word if n == 1 else (plural_word or word + 's')}"
