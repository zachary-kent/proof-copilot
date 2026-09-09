"""Is this text a proof body, and nothing else?  (PLAN.md 8.7, by construction.)

A worker returns a *proof body*: tactic sentences between ``Proof.`` and ``Qed.``.
Everything the gate guarantees rests on that being true, so it is checked
structurally rather than by looking for known-bad words:

* the body must lex cleanly (no unterminated comment or string);
* every sentence must be a bullet, a brace, or a terminated tactic sentence;
* a sentence whose first word is a capitalised vernacular command is rejected unless
  it is on the short allowlist of *queries* (``Check``, ``Search``, ``About``, ...),
  proof-state commands (``Unshelve``, ``Existential``, ...) or ``Set/Unset Printing``.

That rejects ``Qed``/``Abort``/``Admitted``/``Proof`` (breaking out of the proof), every
declaration head, ``Set Nested Proofs Allowed``, every escape hatch, ``Require``,
``Import``, ``Ltac``, ``Instance``, ``Hint``, ``Notation``, ``Opaque``, ``Arguments`` ...
without needing to list them.  ``Print`` is rejected too: its output would land in the
same stream the gate reads ``Print Assumptions`` from.

Tactic-level forbidden tokens (``admit``, ``give_up``) are still checked on the
comment-stripped text.
"""

from __future__ import annotations

import re
from dataclasses import dataclass

from pcp.rocq.lexer import Sentence, first_word, identifiers, skip_comment, skip_string, split_sentences

#: Capitalised first words that are harmless inside a proof body.
ALLOWED_VERNAC: frozenset[str] = frozenset({
    "Check", "Search", "SearchPattern", "SearchRewrite", "SearchHead", "SearchAbout", "About",
    "Show", "Locate", "Compute", "Eval", "Unshelve", "Existential", "Grab", "Optimize", "Info",
    "Guarded", "Validate",
})
#: Wrappers that take a sentence: the wrapped sentence is validated recursively.
WRAPPERS: frozenset[str] = frozenset({"Fail", "Succeed", "Time", "Timeout"})
#: ``Set``/``Unset`` are allowed only for ``Printing`` options.
_SET_PRINTING = re.compile(r"(?:Set|Unset)\s+Printing\b")

#: Matched as identifiers outside comments *and strings*: ``idtac "admit"`` is not an
#: admit, and a regex over comment-stripped text said it was (review finding).
_FORBIDDEN_TACTICS = ("admit", "give_up")
_WRAPPER_ARG = re.compile(r"^(?:Fail|Succeed|Time)\s+|^Timeout\s+\d+\s+")


@dataclass(frozen=True)
class Violation:
    reason: str
    sentence: str

    def render(self) -> str:
        text = " ".join(self.sentence.split())
        if len(text) > 80:
            text = text[:77] + "..."
        return f"{self.reason}: `{text}`"


def lex_issues(text: str) -> list[str]:
    """Structural lexing problems: unterminated comment/string, stray ``*)``."""
    issues: list[str] = []
    i, n = 0, len(text)
    while i < n:
        if text.startswith("(*", i):
            end = skip_comment(text, i)
            if end >= n and not text.rstrip().endswith("*)"):
                issues.append("unterminated comment")
                break
            if end >= n and _comment_depth(text[i:]) != 0:
                issues.append("unterminated comment")
                break
            i = end
        elif text[i] == '"':
            end = skip_string(text, i)
            if end >= n and not _string_closed(text[i:]):
                issues.append("unterminated string literal")
                break
            i = end
        elif text.startswith("*)", i):
            issues.append("stray `*)` outside a comment")
            break
        else:
            i += 1
    return issues


def _comment_depth(text: str) -> int:
    depth = 0
    i, n = 0, len(text)
    while i < n:
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif text.startswith("*)", i):
            depth -= 1
            i += 2
        elif text[i] == '"' and depth:
            i = skip_string(text, i)
        else:
            i += 1
    return depth


def _string_closed(text: str) -> bool:
    i, n = 1, len(text)
    while i < n:
        if text[i] == '"':
            if i + 1 < n and text[i + 1] == '"':
                i += 2
                continue
            return True
        i += 1
    return False


def validate_body(body: str) -> list[Violation]:
    """Every reason ``body`` is not a plain proof body.  Empty means it is one."""
    violations: list[Violation] = [Violation(issue, body[-80:]) for issue in lex_issues(body)]
    if violations:
        return violations
    for sent in split_sentences(body):
        violations.extend(_check_sentence(sent))
    return violations


def _check_sentence(sent: Sentence) -> list[Violation]:
    code = sent.code
    if not code.strip():
        return []
    if sent.is_bullet or sent.is_brace:
        return []
    if not code.rstrip().endswith("."):
        return [Violation("unterminated tactic sentence (missing the final `.`)", code)]
    return _check_code(code)


def _check_code(code: str) -> list[Violation]:
    fw = first_word(code)
    if fw and fw[0].isupper():
        if fw in WRAPPERS:
            inner = _WRAPPER_ARG.sub("", code, count=1)
            if inner == code:
                return [Violation(f"malformed `{fw}` wrapper", code)]
            return _check_code(inner)
        if fw in ("Set", "Unset"):
            if _SET_PRINTING.match(code):
                return []
            return [Violation("`Set`/`Unset` other than `Printing` options is not allowed in a proof body", code)]
        if fw in ALLOWED_VERNAC:
            return []
        if fw in ("Qed", "Defined", "Admitted", "Abort", "Save"):
            return [Violation("a proof body may not end the proof itself", code)]
        if fw == "Proof":
            return [Violation("a proof body may not open a proof", code)]
        return [Violation(f"vernacular command in a proof body: `{fw}`", code)]
    words = set(identifiers(code))
    return [Violation(f"forbidden tactic `{label}`", code) for label in _FORBIDDEN_TACTICS if label in words]


_LEADING_PROOF = re.compile(r"^Proof\b(?:\s+(?:using|with)\b[^.]*)?\s*\.$", re.S)
_TRAILING_ENDER = re.compile(r"^(?:Qed|Defined|Admitted)\s*\.$")


def strip_proof_wrapper(text: str) -> str:
    """Accept a body with or without its ``Proof.``/``Qed.`` wrapper.

    Sentence-based, so a comment before ``Proof.`` or after ``Qed.`` no longer keeps
    the wrapper in place (review finding: the doubled ``Proof.`` was then blamed on
    the proof).  Only a *leading* opener and a *trailing* ender are removed; anything
    in the middle is left for :func:`validate_body` to reject.
    """
    sents = split_sentences(text)
    lo, hi = 0, len(text)
    if sents and _LEADING_PROOF.match(sents[0].code.strip()):
        lo = sents[0].end
        sents = sents[1:]
    while sents and not sents[-1].code.strip():
        hi = sents[-1].start
        sents = sents[:-1]
    if sents and _TRAILING_ENDER.match(sents[-1].code.strip()):
        hi = sents[-1].start
    return text[lo:hi].strip()


def tactic_sentences(body: str) -> list[str]:
    """The body as the list of sentences a replay sends to petanque, comments stripped."""
    return [s.code for s in split_sentences(body) if s.code.strip()]


def is_placeholder(body: str) -> bool:
    """The untouched ``admit.`` stub a packet ships with, or nothing at all."""
    return body.strip() in ("", "admit.", "admit", "Admitted.")
