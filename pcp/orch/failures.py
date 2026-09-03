"""Failure classification, so a benchmark run says *what to fix* (PLAN.md 1, 13).

A solve rate is a number; a failure taxonomy is a work queue.  PLAN.md 1 already
names the failure modes worth counting, roughly in order of how much time they waste,
and the whole design brief rests on the claim that they are *tool* problems rather
than model problems.  That claim is falsifiable, and this is what falsifies it: if a
run's failures are dominated by classes the tooling addresses and the solve rate does
not move when the tooling is switched on, the claim is wrong.

Classification is deterministic and pattern-based, and it is honest about its limits:
anything it cannot place lands in ``unclassified`` rather than being forced into the
nearest bucket.  A taxonomy that always has an answer teaches you nothing.
"""

from __future__ import annotations

import re
from collections import Counter
from dataclasses import dataclass, field
from typing import Iterable

#: The taxonomy.  The first seven are PLAN.md 1's list, in its order; the rest are
#: failures of the *pipeline* rather than of Iris reasoning, and are worth separating
#: because they are fixed in completely different places.
TAXONOMY: dict[str, str] = {
    "premature-consumption": "a spatial hypothesis was eliminated early and needed later",
    "leftover-spatial": "iFrame/done failed because the spatial context was not empty",
    "mask-arithmetic": "invariant masks did not line up (↑N ⊆ E, E ∖ ↑N, open/close pairing)",
    "later-modality": "missing iNext / iMod at the wrong point / ▷ depth mismatch",
    "persistent-vs-spatial": "treated a persistent hypothesis as consumed, or vice versa",
    "retrieval": "referred to a lemma or instance that does not exist",
    "context-pollution": "ran out of context, or drowned in goal dumps",
    "pattern-mismatch": "an iDestruct/iIntros pattern did not fit its object",
    "evaluation-position": "wp_bind/wp_pure could not find the expected redex in the program term",
    "incomplete-proof": "the script ran out of tactics with goals still open",
    "permission-denied": "the harness's own permission layer blocked a command",
    "unification-failure": "iApply/wp_apply could not match a lemma's conclusion to the goal",
    "prophecy-atomicity": "logically atomic bookkeeping: atomic update, commit point, prophecy resolution",
    "no-progress": "the worker looped or made no state progress before its deadline",
    "deadline": "the worker ran out of wall clock",
    "gate-violation": "the patch was rejected by the deterministic gate (admit, global, escape hatch)",
    "protocol-violation": "the worker produced no usable answer in the required shape",
    "contested": "the worker argued the statement itself is wrong",
    "scope-or-type-error": "a term elaborated at the wrong type -- usually a missing %Z/%nat scope",
    "state-tool-error": "a pcp proof-state tool failed to run (often: the file does not compile)",
    "focus-or-bullet": "bullets/braces did not match the goals actually open",
    "specialization": "iSpecialize could not instantiate a wand, or its hypothesis was gone",
    "runner-error": "the provider or its CLI failed; not a proof failure",
    "unclassified": "no rule matched -- read the record",
}

#: (class, regex, weight).  Weight breaks ties when several rules fire; higher wins.
_RULES: list[tuple[str, re.Pattern[str], int]] = [
    # -- Iris reasoning ----------------------------------------------------
    ("leftover-spatial", re.compile(r"spatial context is not empty|iFrame.*cannot|not all resources|cannot solve.*emp", re.I), 6),
    ("pattern-mismatch", re.compile(r"iOrDestruct|iAndDestruct|cannot destruct|pattern/prop mismatch|not a disjunction|intro pattern", re.I), 7),
    ("mask-arithmetic", re.compile(r"mask|↑\w+ ⊆|∖ ↑|fupd_mask|invariant .* already open|not.*disjoint", re.I), 6),
    ("later-modality", re.compile(
        r"iNext|▷|\blater\b|timeless|MaybeIntoLaterN|is not later|"
        r"iModIntro[^\n]*not a modality|goal is not a modality|IntoModal", re.I), 5),
    ("persistent-vs-spatial", re.compile(r"not persistent|IntoPersistent|Persistent .* instance|intuitionistic context", re.I), 6),
    # `wp_bind: cannot find (! ?e)%E in ...` is *not* a retrieval failure: the lemma
    # exists, the program term is not in the shape the tactic expected.  Filing it
    # under retrieval inflated that bucket and hid the mode the state layer's WP
    # expression field addresses directly.
    ("evaluation-position", re.compile(r"wp_(?:bind|pure|apply)[^\n]*cannot find|is not a redex|not a value|no (?:such )?evaluation context", re.I), 9),
    ("retrieval", re.compile(r"was not found in the current environment|Unknown (?:constant|reference)|The reference \S+ was not found|Cannot find an? (?:instance|lemma)", re.I), 8),
    ("incomplete-proof", re.compile(r"Attempt to save an incomplete proof|There are still unproven goals|remaining open goals", re.I), 9),
    ("permission-denied", re.compile(
        r"requires approval|permission to use|was not granted|blocked by the permission|"
        # The CLI's actual wording, which the rule above never matched: a blocked
        # `ls` was filed as an unclassified proof failure seven times.
        r"was blocked\. For security|command contains multiple operations", re.I), 20),
    ("unification-failure", re.compile(r"Unable to unify|cannot unify|not.*convertible|iApply.*failed|no matching clauses|Impossible to unify", re.I), 6),
    ("prophecy-atomicity", re.compile(r"atomic_update|AU |wp_resolve|NewProph|Resolve|commit point|atomic.*abort", re.I), 3),
    ("premature-consumption", re.compile(r"was consumed at step|repair class: (?:split-differently|frame-later)|no such (?:hypothesis|ident)|not found in the context", re.I), 7),
    # The single commonest *statement* defect on these developments, and the one that
    # poisoned a whole seqlock_wf rung: `z = 1 + Z.of_nat ver` parses in `nat_scope`
    # and does not elaborate. It was invisible in the report because Rocq prints the
    # whole environment before the complaint, so the capture kept the dump and lost
    # the verb -- see `collapse_environment`.
    ("scope-or-type-error", re.compile(
        r'The term "[^"]*" has type "[^"]*" while it is expected to have type|'
        r"has type .{0,40} while it is expected to have type|"
        r"Illegal application|Non-functional construction|"
        r"is expected to have type \"?nat|cannot be applied to", re.I), 8),
    ("specialization", re.compile(
        r"iSpecialize[^\n]*(?:cannot instantiate|not found|could not)", re.I), 7),
    # The state layer failing is not the same as a proof failing, and on the run that
    # made this visible it was *downstream* of a design that did not compile: 13
    # `proof_open` failures, every one of them the poisoned file rather than a lemma.
    # Worth its own class precisely because the state layer is what is being ablated.
    ("state-tool-error", re.compile(
        r"Error executing tool (?:mcp__pcp__)?\w+|pet-server|petanque|"
        r"no petanque binary|state \d+ is no longer in the LRU", re.I), 12),
    ("focus-or-bullet", re.compile(
        r"proof is focused, but cannot be unfocused|"
        r"Wrong bullet|No such (?:bullet|goal)|"
        r"[Tt]his subproof is complete|not the last goal", re.I), 8),
    # -- pipeline ----------------------------------------------------------
    ("gate-violation", re.compile(r"no new Admitted|escape hatches|ambient-state hygiene|axiom hygiene|statement pinning", re.I), 9),
    ("protocol-violation", re.compile(r"produced no answer\.json|malformed answer\.json|no fenced proof block|no scripted answer", re.I), 9),
    # The decomposer's parser rejects on *shape*, and that verdict is definite: it
    # says exactly what was wrong and no reading of the transcript can overturn it.
    # Left to compete on weight, a round that died on a pair of braces was filed as
    # `mask-arithmetic`, because the design prose it was rejected for contains masks.
    ("protocol-violation", re.compile(
        r"must be an object|must be a list|is not a Rocq identifier|is not an identifier|"
        r"has no statement|has no text|produced no JSON object|is not a Require line", re.I), 19),
    ("deadline", re.compile(r"exceeded its .* deadline|timed out|Timeout", re.I), 8),
    ("no-progress", re.compile(r"showed no progress|loop detected|state hash repeat", re.I), 8),
    # Infrastructure failures outrank everything: a sandbox that cannot start looks
    # exactly like a worker that produced no answer, and blaming the worker sends you
    # to debug the prompt instead of the harness.  (This rule exists because that is
    # precisely what happened on the first benchmark run.)
    ("runner-error", re.compile(
        # `OAuth access token has been revoked` reached the report as "the decomposer
        # produced no JSON object to read" -- true, and useless: it sent the reader
        # looking at the prompt when the credential had expired mid-ladder.
        r"is not on PATH|unauthenticated|API call|provider error|rate limit|"
        r"Failed to authenticate|access token has been revoked|401|invalid[_ ]api[_ ]key|"
        r"bwrap:|Can't find source path|execvp|No such file or directory: '/tmp/pcp-|"
        r"Permission denied|command not found|Input must be provided", re.I), 20),
    ("context-pollution", re.compile(r"context (?:window|length) exceeded|too many tokens|prompt is too long", re.I), 10),
]

#: Classes a *transcript* may establish on its own, against evidence that already
#: says something.  These are the harness failing underneath the worker, and the
#: transcript is usually the only place they surface at all -- a sandbox that cannot
#: start looks exactly like a worker that produced no answer.  The rest of the
#: taxonomy describes a proof going wrong, and a transcript is mostly the worker's
#: own prose: Iris vocabulary there says what it was writing about, not what failed.
_FROM_CONTEXT = frozenset(
    {"runner-error", "permission-denied", "context-pollution", "deadline", "no-progress"}
)

#: Rocq's syntax errors are almost always the *worker's* formatting, not a reasoning
#: failure, and lumping them in with retrieval failures would flatter the tooling.
_SYNTAX = re.compile(r"Syntax error|expected after|Illegal begin of|Unexpected token", re.I)

#: Tool results that are not error reports at all.  A worker that greps a source file
#: gets its contents back, and a docstring mentioning "Error" is not an error -- one
#: run classified a chunk of `gate.py` as a proof failure.
_NOT_AN_ERROR = re.compile(
    # `in line: 545 return ...` is a grep hit reported mid-string rather than at the
    # start of one, so the `^\s*\d+[:\t]` anchor missed it and a chunk of this very
    # file was recorded as a proof failure.
    # `Exit code 1` followed by a bare file listing is the worker running `ls` in its
    # own workdir, not a proof failure -- 36 records in one rwcas run were noise of
    # this kind, in the very report the noise makes harder to read.
    r'^\s*(?:"""|\#|/\*)|^\s*\d+[:\t]|\bin line:|PLAN\.md|def \w+\(|import \w+'
    r'|^\s*Exit code \d+\s*$', re.M
)

#: The packet's own filenames.  A line made only of these is a directory listing.
_PACKET_FILES = ("_CoqProject", "pcp-node.json", "TASK.md", "answer.json", "proof.v", ".mcp.json")


#: How Rocq's type errors actually start complaining, after the environment dump.
_COMPLAINT = (
    r"(?:The term\b|Unable to unify\b|Cannot \w|Illegal\b|The reference\b|Found no\b"
    r"|Impossible to unify\b|In the projection\b|No such\b|The command has indeed failed\b)"
)
_ENVIRONMENT_DUMP = re.compile(r"In environment\b.*?(?=" + _COMPLAINT + ")", re.S)


#: `pcp check` appends its own diagnosis to a failing compile, and a JSON tool result
#: carries it in a `"diagnosis"` field. That text is *ours*: it names modalities, mask
#: arithmetic and candidate tactics by design, so classifying it labels the failure
#: with whatever our diagnostic vocabulary happened to mention rather than with what
#: went wrong. Measured: an `iIntro` failure became `mask-arithmetic` this way.
_DIAGNOSIS_FIELD = re.compile(r'["\']?diagnosis["\']?\s*:\s*"(?:[^"\\]|\\.)*"', re.S)


def strip_our_own_diagnosis(text: str) -> str:
    """Drop the diagnosis `pcp check` attached, keeping the error it explains.

    Same principle as the guard that stops a worker grepping `failures.py` from
    teaching the classifier that a proof failed: the taxonomy must read the compiler,
    never the harness.
    """
    return _DIAGNOSIS_FIELD.sub("", text or "")


def collapse_environment(text: str) -> str:
    """Drop Rocq's `In environment` binder dump, keeping the complaint after it.

    A type error inside an Iris proof prints every binder and typeclass instance in
    scope before it says what is wrong, which on these developments runs past any
    sane capture limit. So the limit kept the dump and discarded the verb: 53 errors
    in one run were recorded as the unclassifiable fragment `In environment Σ :
    gFunctors`, and the thing that would have classified them -- `The term "..." has
    type "Z" while it is expected to have type "nat"` -- was cut off.

    Only collapses when a complaint is actually found after the dump; an error shaped
    differently is left whole rather than mangled on a guess.
    """
    return _ENVIRONMENT_DUMP.sub("In environment [...] ", text or "")


def looks_like_an_error(text: str) -> bool:
    """Cheap guard against classifying file contents the worker happened to read."""
    if not text or len(text.strip()) < 5:
        return False
    if _NOT_AN_ERROR.search(text[:200]) and not re.search(r"^\s*Error:", text, re.M):
        return False
    if _is_a_directory_listing(text):
        return False
    return True


def _is_a_directory_listing(text: str) -> bool:
    """`Exit code 1` + the packet's own filenames is a worker running `ls`."""
    words = [w for w in re.split(r"[\s,]+", text.strip()) if w]
    if not words or len(words) > 16:
        return False
    hits = sum(1 for w in words if w in _PACKET_FILES or w.endswith(".v") or w.startswith("Exit"))
    return hits >= 2 and hits >= len(words) - 2


@dataclass
class Finding:
    klass: str
    evidence: str = ""
    confidence: str = "certain"

    @property
    def description(self) -> str:
        return TAXONOMY.get(self.klass, "")


@dataclass
class Classification:
    findings: list[Finding] = field(default_factory=list)

    @property
    def primary(self) -> str:
        return self.findings[0].klass if self.findings else "unclassified"

    @property
    def classes(self) -> list[str]:
        return [f.klass for f in self.findings]

    def render(self) -> str:
        if not self.findings:
            return "unclassified"
        return ", ".join(f"{f.klass}" + ("?" if f.confidence != "certain" else "") for f in self.findings)


def classify(
    *sources: str | None, status: str = "stuck", context: str | None = None
) -> Classification:
    """Classify one failed attempt from whatever text is available.

    Pass the worker's evidence, the gate's report and the raw compiler output; the
    order does not matter.  Returns every class that fired, most specific first.

    `context` is the worker's transcript, and it is deliberately weaker than the
    rest: it is consulted only when nothing else fired.  A transcript is mostly the
    worker's own writing, and Iris writing is full of the words the taxonomy matches
    on -- a decomposer round rejected for malformed JSON was filed as
    `mask-arithmetic`, with a lemma statement *it had proposed* quoted back as the
    evidence.  A taxonomy that confident about the wrong thing is worse than
    `unclassified`, because the whole point of it is to say what to build next.
    """
    if status == "contested":
        return Classification([Finding("contested")])
    primary = "\n".join(s for s in sources if s)
    found = _classify_text(primary)
    if not context:
        return found
    widened = _classify_text("\n".join(x for x in (primary, context) if x))
    # With no evidence at all the transcript is all there is -- often it holds the
    # compiler error the worker never got to report.
    if found.primary == "unclassified":
        return widened
    # Otherwise the transcript may only reveal the harness failing underneath the
    # worker, never re-diagnose the proof.
    if widened.primary in _FROM_CONTEXT:
        return widened
    return found


def _classify_text(text: str) -> Classification:
    if not text.strip():
        return Classification([Finding("unclassified", "no evidence was recorded")])
    if not looks_like_an_error(text):
        return Classification([Finding("unclassified", "not an error report: " + _tail(text, 80))])

    hits: list[tuple[int, Finding]] = []
    for klass, pattern, weight in _RULES:
        m = pattern.search(text)
        if m:
            hits.append((weight, Finding(klass, _context(text, m))))
    if not hits:
        if _SYNTAX.search(text):
            return Classification([Finding("protocol-violation", "Rocq syntax error in the worker's script")])
        return Classification([Finding("unclassified", _tail(text))])
    hits.sort(key=lambda h: -h[0])
    return Classification([f for _, f in hits])


def _context(text: str, m: re.Match[str], width: int = 90) -> str:
    start = max(0, m.start() - width // 2)
    return " ".join(text[start : m.end() + width // 2].split())


def _tail(text: str, n: int = 200) -> str:
    return " ".join(text.strip().split())[-n:]


# ------------------------------------------------------------------- aggregation

@dataclass
class FailureReport:
    total: int = 0
    solved: int = 0
    primary: Counter = field(default_factory=Counter)
    all_classes: Counter = field(default_factory=Counter)
    examples: dict[str, list[str]] = field(default_factory=dict)
    #: Classes workers hit and *recovered from*.  Counted separately because they
    #: are the cheapest wins available: the capability is already there, the tooling
    #: is just making it pay for it in turns.
    friction: Counter = field(default_factory=Counter)
    friction_examples: dict[str, list[str]] = field(default_factory=dict)
    turns: list[int] = field(default_factory=list)
    checks: list[int] = field(default_factory=list)

    def render(self, limit: int = 3) -> str:
        failed = self.total - self.solved
        lines = [f"{self.solved}/{self.total} solved · {failed} failed"]
        if self.turns or self.checks:
            lines.append(
                f"  effort: {_mean(self.turns):.1f} turns, {_mean(self.checks):.1f} "
                "gate checks per attempt"
            )
        if self.primary:
            lines.append("")
            lines.append("failures, by primary class:")
            width = max(len(k) for k in self.primary)
            for klass, n in self.primary.most_common():
                share = 100 * n / max(1, failed)
                lines.append(f"  {klass:<{width}}  {n:>3}  {share:4.0f}%   {TAXONOMY.get(klass, '')}")
                for ex in self.examples.get(klass, [])[:limit]:
                    lines.append(f"      · {ex[:140]}")
            secondary = [k for k, _ in self.all_classes.most_common() if k not in self.primary]
            if secondary:
                lines.append("  also present (not primary): " + ", ".join(secondary))
        if self.friction:
            lines.append("")
            lines.append("friction -- errors workers recovered from (including on solves):")
            width = max(len(k) for k in self.friction)
            for klass, n in self.friction.most_common():
                lines.append(f"  {klass:<{width}}  {n:>3}   {TAXONOMY.get(klass, '')}")
                for ex in self.friction_examples.get(klass, [])[:limit]:
                    lines.append(f"      · {ex[:140]}")
        if not self.primary and not self.friction:
            lines.append("  (nothing to report -- no failures and no recorded friction)")
        return "\n".join(lines)


def _mean(values: list[int]) -> float:
    return sum(values) / len(values) if values else 0.0


_ESCAPE = re.compile(r'\\u([0-9a-fA-F]{4})|\\(["\\\\/nrt])')
_SIMPLE = {'"': '"', "\\": "\\", "/": "/", "n": "\n", "r": "\r", "t": "\t"}
_UNICODE_ESCAPE = re.compile(r"\\u[0-9a-fA-F]{4}")


def unescape(text: str) -> str:
    """Decode a JSON-escaped fragment so the classifier can read it.

    The state tools return JSON, and a failing `proof_step` reaches the trace as the
    body of a JSON string: `iMod: cannot eliminate modality\\n(\\u25b7 inv)`. Every
    rule in this file is written against Iris' actual notation, so `\\u25b7` matched
    nothing and the largest bucket in one rwcas report was `unclassified` -- the
    tools' own output, invisible to the tooling meant to read it.

    Not `json.loads`: these are fragments of a larger document and frequently have
    unbalanced quotes, so only the escapes are decoded and everything else is left
    exactly as it is.
    """
    # Doubly escaped in practice: the tool's JSON is embedded in the trace's JSON, so
    # the notation arrives as `\\u2217`. One pass turns that into `\u2217`, which is
    # still not `∗`. Repeat while an escape sequence survives, bounded, and stop the
    # moment a pass changes nothing -- a lone backslash in a path must come out whole.
    for _ in range(3):
        if "\\" not in text:
            break
        nxt = _ESCAPE.sub(
            lambda m: chr(int(m.group(1), 16)) if m.group(1) else _SIMPLE[m.group(2)], text
        )
        if nxt == text or not _UNICODE_ESCAPE.search(nxt):
            return nxt
        text = nxt
    return text


def summarize(records: Iterable[dict]) -> FailureReport:
    """Aggregate per-attempt records into a work queue."""
    report = FailureReport()
    for rec in records:
        report.total += 1
        trace = rec.get("trace") or {}
        if trace.get("turns"):
            report.turns.append(int(trace["turns"]))
        if trace.get("check_iterations") is not None:
            report.checks.append(int(trace["check_iterations"]))
        for err in trace.get("errors", []):
            # Guarded here as well as at capture time. The capture-time guard only
            # protects records written *after* it lands, and the report is exactly
            # where the noise does its damage -- it crowds out the findings it is
            # printed next to.
            text = collapse_environment(strip_our_own_diagnosis(unescape(str(err))))
            if not looks_like_an_error(text):
                continue
            c = classify(text)
            report.friction[c.primary] += 1
            report.friction_examples.setdefault(c.primary, []).append(
                f"{rec.get('lemma', '?')}: {' '.join(text.split())[:120]}"
            )
        if rec.get("solved"):
            report.solved += 1
            continue
        c = classify(
            collapse_environment(strip_our_own_diagnosis(unescape(rec.get("evidence") or ""))),
            rec.get("gate_report"),
            rec.get("compile_output"),
            rec.get("transcript_tail"),
            status=rec.get("status", "stuck"),
        )
        report.primary[c.primary] += 1
        for klass in c.classes:
            report.all_classes[klass] += 1
        label = f"{rec.get('lemma', '?')}: {c.findings[0].evidence if c.findings else ''}"
        report.examples.setdefault(c.primary, []).append(label)
    return report
