"""Shaping Rocq error text, and finding the error a document hits before a lemma.

Rocq puts the *cause* of an elaboration error last: ``In environment`` and a binder
dump of any length come first, and ``The term ... has type ... while it is expected to
have type ...`` after it.  A head-only cut (``text[:500]``) therefore keeps exactly the
part nobody needs, so every cut of Rocq text in the state layer and the MCP results
goes through :func:`shape_error`, which drops the dump first and then keeps both ends.

petanque's ``start`` reports a failure *at the lemma* ("Theorem not found", "Theorem
found but failed with Coq error: The reference X was not found") even when the cause
is a ``Require`` fifty lines earlier.  :func:`check_prefix` recompiles the statements
up to the lemma with the project's own ``coqc`` and names the first error in source
coordinates -- the one fact the lemma-local symptom hides.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, replace
from pathlib import Path

from pcp.config.toolchain import project_root
from pcp.rocq.decls import parse_blocks, scopes_at
from pcp.rocq.lexer import split_sentences
from pcp.rocq.project import compile_text, coq_project_flags
from pcp.util.io import read_text

#: Default size of a shaped error: what an MCP result or an exception message carries.
DEFAULT_ERROR_CHARS = 1500
#: Budget of the diagnostic prefix compile.  It re-checks what petanque already checked,
#: so it is bounded well below ``start``'s own wall clock.
DEFAULT_PREFIX_TIMEOUT = 120.0

#: What follows an ``In environment`` dump: the complaint itself.
COMPLAINT = (
    r"(?:The term\b|Unable to unify\b|Cannot \w|Illegal\b|The reference\b|Found no\b"
    r"|Impossible to unify\b|In the projection\b|No such\b|The command has indeed failed\b"
    r"|The type\b|The \d+(?:st|nd|rd|th) term\b|Unbound\b|Ill-typed\b)"
)
ENVIRONMENT_DUMP = re.compile(r"In environment\b.*?(?=" + COMPLAINT + ")", re.S)
ELISION = " […] "


def collapse_environment(text: str) -> str:
    """Drop Rocq's ``In environment`` binder dump, keeping the complaint after it."""
    return ENVIRONMENT_DUMP.sub("In environment [...] ", text or "")


def shape_error(text: str | None, limit: int = DEFAULT_ERROR_CHARS) -> str:
    """``text`` cut to ``limit`` characters without losing its cause.

    Text that fits is returned untouched (the binder dump is useful when there is room
    for it).  Otherwise the dump goes first, and if that is not enough the *middle* is
    elided: the head says which command failed, the tail says why.
    """
    text = (text or "").strip()
    if len(text) <= limit:
        return text
    text = collapse_environment(text)
    if len(text) <= limit:
        return text
    head = max(0, limit // 3)
    tail = max(0, limit - head - len(ELISION))
    return text[:head].rstrip() + ELISION + text[len(text) - tail :].lstrip()


# --------------------------------------------------------------- prefix check


@dataclass(frozen=True)
class PrefixCheck:
    """What ``coqc`` says about the source up to (and including) a lemma's statement."""

    thm: str
    file: str
    ok: bool
    timed_out: bool = False
    elapsed_s: float = 0.0
    budget_s: float = 0.0
    #: 1-based line and column of the first error (or of the sentence being checked
    #: when the budget ran out), in the *source* file.
    line: int | None = None
    column: int | None = None
    sentence: str = ""
    message: str = ""
    #: The error is in the lemma's own statement, not before it.
    in_statement: bool = False
    #: coqc could not be run at all.
    unavailable: str = ""

    @property
    def where(self) -> str:
        return f"{self.file}:{self.line}" if self.line is not None else self.file

    def render(self) -> str:
        """One sentence naming the cause, or ``""`` when coqc found nothing wrong."""
        if self.unavailable:
            return ""
        quoted = f" `{_one_line(self.sentence, 100)}`" if self.sentence else ""
        if self.timed_out:
            at = f"; coqc was still checking {self.where}{quoted} after {self.elapsed_s:.0f} s" if self.line else ""
            return f"the statements up to {self.thm} do not check within {self.budget_s:g} s{at}"
        if self.ok:
            return ""
        if self.in_statement:
            return f"the statement of {self.thm} does not elaborate: {self.where}: {self.message}"
        return f"the document does not check before {self.thm}: {self.where}{quoted}: {self.message}"


def check_text(source: str, thm: str) -> tuple[str, int] | None:
    """The source up to ``thm``'s statement, proofs admitted, **line numbers preserved**.

    Each ``Qed`` body is replaced by as many newlines as it spanned and ``Admitted.``, so
    a line coqc reports is the source's line -- no offset map needed.  The lemma itself
    is admitted and its open sections/modules closed.  Returns the text and the offset
    of the lemma's statement, or ``None`` when the file declares no ``thm``.
    """
    sentences = split_sentences(source)
    blocks = parse_blocks(source, sentences=sentences)
    target = next((b for b in blocks if b.name == thm), None)
    if target is None:
        return None
    out: list[str] = []
    cursor = 0
    for b in blocks:
        if b is target:
            break
        if not (b.kind == "script" and b.ender == "Qed" and b.body_start is not None and b.ender_end is not None):
            continue
        out.append(source[cursor : b.body_start])
        out.append("\n" * source.count("\n", b.body_start, b.ender_end) + " Admitted.")
        cursor = b.ender_end
    out.append(source[cursor : target.statement_end])
    if target.kind == "script":
        out.append("\nAdmitted.")
    for scope in reversed(scopes_at(sentences, target.statement_start)):
        out.append(f"\nEnd {scope.name}.")
    return "".join(out) + "\n", target.statement_start


_LOCATED = re.compile(r'^File "[^"]*", line (?P<line>\d+), characters (?P<a>\d+)-(?P<b>\d+):\s*$', re.M)
_TIMED = re.compile(r"^Chars (?P<a>\d+) - (?P<b>\d+) \[", re.M)


def check_prefix(
    path: str | Path,
    thm: str,
    *,
    root: str | Path | None = None,
    timeout: float = DEFAULT_PREFIX_TIMEOUT,
    source: str | None = None,
) -> PrefixCheck | None:
    """Compile the statements up to ``thm`` with ``root``'s ``coqc``; report the first error.

    ``None`` when the file has no ``thm`` (the caller says so itself).  ``-time`` makes
    coqc report each sentence as it finishes -- through a pipe, as it goes -- so a
    budget overrun still names the sentence that was being checked.
    """
    src_path = Path(path).resolve()
    text = source if source is not None else read_text(src_path)
    built = check_text(text, thm)
    if built is None:
        return None
    check, stmt_at = built
    proj = Path(root).resolve() if root is not None else (project_root(src_path) or src_path.parent)
    try:
        shown = str(src_path.relative_to(proj))
    except ValueError:
        shown = str(src_path)
    result = compile_text(
        check,
        filename=f"{_module_name(src_path.stem)}_pcpcheck.v",
        root=proj,
        flags=[*coq_project_flags(proj), "-time"],
        timeout=timeout,
    )
    base = PrefixCheck(thm=thm, file=shown, ok=False, elapsed_s=result.elapsed_s, budget_s=timeout)
    if result.unavailable:
        return replace(base, unavailable=result.unavailable)
    stmt_line = check.count("\n", 0, stmt_at) + 1
    if result.timed_out:
        at = _running_sentence(check, result.stdout)
        if at is None:
            return replace(base, timed_out=True)
        line, col, sent = at
        return replace(base, timed_out=True, line=line, column=col, sentence=sent, in_statement=line >= stmt_line)
    if result.ok:
        return replace(base, ok=True)
    located = _first_error(result.output)
    if located is None:
        return replace(base, message=shape_error(result.output, 600))
    line, char, message = located
    return replace(
        base, line=line, column=char + 1, sentence=_sentence_at(check, line, char), message=message,
        in_statement=line >= stmt_line,
    )


def _first_error(output: str) -> tuple[int, int, str] | None:
    """``(line, char, message)`` of the first *error* coqc located (warnings are skipped)."""
    matches = list(_LOCATED.finditer(output))
    for i, m in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(output)
        body = output[m.end() : end]
        body = _TIMED.split(body)[0] if _TIMED.search(body) else body
        stripped = body.strip()
        if not stripped.startswith("Error"):
            continue
        message = re.sub(r"^Error:\s*", "", stripped)
        return int(m.group("line")), int(m.group("a")), shape_error(" ".join(message.split()), 800)
    return None


def _running_sentence(text: str, timings: str) -> tuple[int, int, str] | None:
    """The sentence after the last one ``-time`` reported: the one the budget ran out on."""
    done = max((int(m.group("b")) for m in _TIMED.finditer(timings)), default=0)
    for sent in split_sentences(text):
        if not sent.code.strip():
            continue
        if len(text[: sent.code_start].encode("utf-8")) >= done:  # coqc counts bytes
            line = text.count("\n", 0, sent.code_start) + 1
            col = sent.code_start - (text.rfind("\n", 0, sent.code_start) + 1) + 1
            return line, col, sent.code
    return None


def _sentence_at(text: str, line: int, char: int) -> str:
    """The sentence covering coqc's ``line``/``char`` (a byte offset into that line)."""
    lines = text.split("\n")
    if not 1 <= line <= len(lines):
        return ""
    before = "\n".join(lines[: line - 1])
    offset = len(before) + (1 if line > 1 else 0)
    offset += len(lines[line - 1].encode("utf-8")[:char].decode("utf-8", "ignore"))
    for sent in split_sentences(text):
        if sent.start <= offset < sent.end and sent.code.strip():
            return sent.code
    return ""


def _module_name(stem: str) -> str:
    """A stem coqc accepts as a module name (letters, digits, ``_``, ``'``; not a digit first)."""
    name = re.sub(r"[^A-Za-z0-9_']", "_", stem) or "check"
    return name if not name[0].isdigit() else f"m{name}"


def _one_line(text: str, width: int) -> str:
    one = " ".join(text.split())
    return one if len(one) <= width else one[: width - 1] + "…"
