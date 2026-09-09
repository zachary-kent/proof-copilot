"""Provider outages: recognise one, wait it out, resume (PLAN.md 6, 8.11, 11).

A long run used to end when the provider blinked: a revoked or expired login, "You've
hit your session limit · resets 9:50pm", a network failure.  The graph survived
(resume, salvage, bounded attempts) but nobody restarted the run, and PLAN.md 11 is
explicit that an outage is not a proof failure: unused window capacity expires
worthless, so the run should *wait for the window* rather than park every node and
report ``error``.  This module is the vocabulary for that:

* :func:`detect_outage` reads an ``error`` result -- and only an ``error``; a worker's
  ``stuck`` is never an outage however it is worded -- with word-bounded patterns,
  the way :mod:`pcp.orch.failures` reads everything else (``401`` is never a bare
  substring: a compile error on line 401 is a compile error).  The Claude CLI's
  64k output ceiling is *not* an outage: it is handled by the runner's env default
  (:data:`pcp.config.env.CLAUDE_MAX_OUTPUT_TOKENS`) and returns ``None`` here.
* :func:`wait_for_provider` sleeps until the window resets when the message said
  when, then probes with a bounded backoff until the provider answers or the wait
  budget is spent.  A probe that cannot tell (``None``) counts as "back" after one
  backoff step: a runner that cannot be asked must never block a run forever.
* :class:`ProviderPause` is the one pause a run has: the first outage holds it,
  later outages join it, and every dispatcher waits on its event before starting
  anything new while in-flight attempts run on.
"""

from __future__ import annotations

import asyncio
import re
import time
from collections.abc import Awaitable, Callable
from dataclasses import dataclass
from typing import Any

from pcp.config.env import with_runner_defaults
from pcp.orch.protocol import NodeResult
from pcp.util.proc import run_async
from pcp.util.text import one_line

__all__ = [
    "BACKOFF_S",
    "DEFAULT_MAX_WAIT_S",
    "KINDS",
    "Outage",
    "PausePolicy",
    "ProviderPause",
    "claude_probe",
    "detect_outage",
    "format_wait",
    "parse_reset_time",
    "provider_probe",
    "wait_for_provider",
]

KINDS: tuple[str, ...] = ("unauthenticated", "rate_limited", "provider_unreachable", "cli_missing")
#: Probe cadence: quick at first (a login takes a minute), then no more than one
#: probe per five minutes -- a probe is a real request against the window.
BACKOFF_S: tuple[float, ...] = (30.0, 60.0, 120.0, 300.0)
DEFAULT_MAX_WAIT_S = 12 * 3600.0
PROBE_TIMEOUT_S = 60.0
#: The window resets at a minute, not an instant; probe a little after it.
RESET_GRACE_S = 60.0
#: A provider that answered the probe and then failed the very next attempt is not
#: back; a second outage this soon after a resume backs off before probing again.
REPAUSE_GRACE_S = 120.0

Probe = Callable[[], Awaitable[bool | None]]

HINTS: dict[str, str] = {
    "unauthenticated": "run `claude` `/login` (or `codex login`)",
    "rate_limited": "waiting for the usage window to reset",
    "provider_unreachable": "check the network and the provider's status",
    "cli_missing": "install the CLI and log in",
}

_I = re.IGNORECASE
_OUTPUT_CEILING = re.compile(r"exceeded the \d+ output token maximum", _I)
#: Ordered: a spawn failure is definitive; a login problem outranks a generic "API
#: Error"; a rate limit outranks it too (it carries the reset time).
_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    (
        "cli_missing",
        re.compile(
            r"is not on PATH|could not be started|command not found|\bexecvp\b|No such file or directory|"
            r"\bENOENT\b|is not installed|runs in-process and cannot be sandboxed",
            _I,
        ),
    ),
    (
        "unauthenticated",
        re.compile(
            r"\bunauthenticated\b|\bunauthorized\b|Failed to authenticate|authentication[ _](?:error|failed)|"
            r"(?:access )?token (?:has been |was |is )?(?:revoked|expired)|(?:revoked|expired) (?:access )?token|"
            r"please run /login|\brun /login\b|`/login`|\bnot logged in\b|\blog(?:ged)? in again\b|"
            r"\b(?:HTTP|status|code|error)\s*:?\s*401\b|\b401\s+(?:Unauthorized|OAuth|authentication)|"
            r"invalid[ _]api[ _]key|\bOAuth\b.{0,60}\b(?:revoked|expired|invalid)",
            _I,
        ),
    ),
    (
        "rate_limited",
        re.compile(
            r"session limit|usage limit|rate[ -]limit(?:ed|s)?\b|too many requests|"
            r"\b(?:HTTP|status|code|error)\s*:?\s*429\b|\b429\s+(?:Too Many|rate)|"
            r"\bquota\b.{0,40}\b(?:exceeded|exhausted|reached)|\brate_limit_error\b|\bresets? (?:at |in )?\d",
            _I,
        ),
    ),
    (
        "provider_unreachable",
        re.compile(
            r"connection (?:error|refused|reset|timed out|failed)|\bECONNREFUSED\b|\bECONNRESET\b|\bETIMEDOUT\b|"
            r"\bENOTFOUND\b|\bEAI_AGAIN\b|\bgetaddrinfo\b|network (?:error|is unreachable|failure|is down)|"
            r"Could not resolve host|Temporary failure in name resolution|\bDNS\b.{0,40}\b(?:fail|error|resol)|"
            r"\b(?:HTTP|status|code|error)\s*:?\s*5\d\d\b|\b5\d\d\s+(?:Internal Server Error|Bad Gateway|Service Unavailable|Gateway Time-?out)|"
            r"internal server error|service unavailable|bad gateway|gateway time-?out|\boverloaded(?:_error)?\b|"
            r"\bAPI Error\b|API call failed|provider error|\bfetch failed\b|socket hang up|"
            r"\bupstream (?:error|connect)|\bunable to (?:connect|reach)\b|TLS handshake",
            _I,
        ),
    ),
)
_RESETS_AT = re.compile(r"\bresets?\s+(?:at\s+)?(\d{1,2})(?::(\d{2}))?\s*(am|pm)?\b", _I)
_RESETS_IN = re.compile(r"\bresets?\s+in\s+(?:(\d+)\s*h(?:ours?|rs?)?)?\s*(?:(\d+)\s*m(?:in(?:ute)?s?)?)?", _I)

# Monkeypatch points for tests (sleeps and the clock).
_sleep = asyncio.sleep
_now = time.time


@dataclass(frozen=True)
class Outage:
    """A provider failure underneath a worker.  ``retryable``: waiting can help."""

    kind: str
    detail: str
    resume_at: float | None = None
    retryable: bool = True

    @property
    def hint(self) -> str:
        return HINTS.get(self.kind, "")

    def describe(self) -> str:
        text = f"{self.kind} -- {self.hint}" if self.hint else self.kind
        if self.detail:
            text += f" ({one_line(self.detail, 160)})"
        if self.resume_at is not None:
            text += f"; window resets at {time.strftime('%H:%M', time.localtime(self.resume_at))}"
        return text

    def to_json(self) -> dict[str, Any]:
        return {"kind": self.kind, "detail": self.detail, "resume_at": self.resume_at, "retryable": self.retryable}

    @classmethod
    def from_json(cls, data: dict[str, Any]) -> Outage:
        resume_at = data.get("resume_at")
        return cls(
            kind=str(data.get("kind", "")), detail=str(data.get("detail", "") or ""),
            resume_at=float(resume_at) if resume_at is not None else None,
            retryable=bool(data.get("retryable", True)),
        )


@dataclass(frozen=True)
class PausePolicy:
    """How long a run may wait for its provider (``--pause-hours``; ``0`` disables)."""

    max_wait_s: float = DEFAULT_MAX_WAIT_S
    enabled: bool = True

    @classmethod
    def from_hours(cls, hours: float) -> PausePolicy:
        hours = float(hours or 0)
        return cls(max_wait_s=max(0.0, hours) * 3600.0, enabled=hours > 0)

    @property
    def active(self) -> bool:
        return self.enabled and self.max_wait_s > 0


# ------------------------------------------------------------------ recognition


def parse_reset_time(text: str, *, now: float | None = None) -> float | None:
    """``resets 9:50pm`` -> that wall-clock time today in the machine's local zone, or
    tomorrow if it has already passed; ``resets in 2h 15m`` -> now plus that.  The
    message names a zone (``(America/New_York)``); the machine's own is used, which
    is right on the machine that hit the limit and off by the zone difference on any
    other -- the probe loop corrects that."""
    current = _now() if now is None else now
    m = _RESETS_AT.search(text or "")
    if m:
        hour, minute, ampm = int(m.group(1)), int(m.group(2) or 0), (m.group(3) or "").lower()
        if ampm:
            hour = hour % 12 + (12 if ampm == "pm" else 0)
        if hour > 23 or minute > 59:
            return None
        local = time.localtime(current)
        candidate = time.mktime((local.tm_year, local.tm_mon, local.tm_mday, hour, minute, 0, 0, 0, -1))
        if candidate <= current:
            candidate = time.mktime((local.tm_year, local.tm_mon, local.tm_mday + 1, hour, minute, 0, 0, 0, -1))
        return candidate
    m = _RESETS_IN.search(text or "")
    if m and (m.group(1) or m.group(2)):
        return current + 3600.0 * int(m.group(1) or 0) + 60.0 * int(m.group(2) or 0)
    return None


def _sources(result: NodeResult) -> list[str]:
    """Where an outage announces itself, most specific first."""
    trace = result.trace if isinstance(result.trace, dict) else {}
    out = [str(result.evidence or "")]
    out.append(str(trace.get("result_detail") or ""))
    out.append(str(trace.get("result_error") or ""))
    lines = trace.get("stderr_lines")
    if isinstance(lines, list):
        out.extend(str(line) for line in lines)
    return [s for s in out if s.strip()]


def detect_outage(result: NodeResult, *, now: float | None = None) -> Outage | None:
    """The outage an ``error`` result reports, or ``None`` (module docstring).

    Only ``status == "error"`` is read: that status is reserved for the
    infrastructure by :mod:`pcp.orch.protocol`, so a worker cannot claim an outage
    and a ``stuck`` that quotes a 401 is still the worker's own failure.
    """
    if result.status != "error":
        return None
    sources = _sources(result)
    joined = "\n".join(sources)
    if _OUTPUT_CEILING.search(joined):
        return None
    kind = ""
    detail = ""
    if result.exit_code in (126, 127):
        kind, detail = "cli_missing", sources[0] if sources else f"the runner exited with status {result.exit_code}"
    else:
        for candidate, pattern in _PATTERNS:
            for source in sources:
                if pattern.search(source):
                    kind, detail = candidate, source
                    break
            if kind:
                break
    if not kind:
        return None
    resume_at = parse_reset_time(joined, now=now) if kind == "rate_limited" else None
    return Outage(kind=kind, detail=one_line(detail, 300), resume_at=resume_at, retryable=kind != "cli_missing")


# ------------------------------------------------------------------ probing


def _unwrap(runner: Any) -> Any:
    """A ``SandboxedRunner`` probes through its inner runner: the probe runs on the
    host, outside any attempt's sandbox."""
    seen = 0
    while hasattr(runner, "inner") and seen < 4:
        runner = runner.inner
        seen += 1
    return runner


def _is_claude(runner: Any) -> bool:
    executable = str(getattr(runner, "executable", "") or getattr(runner, "binary", "") or "")
    name = str(getattr(runner, "name", "") or "")
    return executable == "claude" or name.startswith("claude")


async def claude_probe(*, binary: str = "claude", timeout: float = PROBE_TIMEOUT_S, env: dict[str, str] | None = None) -> bool | None:
    """The cheapest real request: ``claude -p`` with every tool disabled, one line in,
    one word out.  ``True`` when it answered, ``False`` when it ran and could not,
    ``None`` when the binary is not there to ask."""
    argv = [binary, "-p", "--output-format", "text", "--tools", "", "--strict-mcp-config"]
    streamed = await run_async(argv, timeout=timeout, stdin="Reply with exactly: ok", env=with_runner_defaults(env))
    if streamed.spawn_error:
        return None
    if streamed.timed_out or streamed.returncode != 0:
        return False
    return "ok" in streamed.text.lower()


def provider_probe(runner: Any) -> Probe:
    """How to ask ``runner``'s provider whether it is back.

    A runner with a real ``auth_check`` (codex: ``codex login status``) is asked
    through :meth:`CLIRunner.authenticated`; a claude-based runner gets
    :func:`claude_probe` (its ``authenticated`` cannot tell); anything else with an
    ``authenticated`` coroutine is asked and may say ``None``; a runner with none
    always says ``None`` -- which :func:`wait_for_provider` treats as "back" after one
    backoff step rather than blocking forever.
    """
    inner = _unwrap(runner)
    authenticated = getattr(inner, "authenticated", None)
    if getattr(inner, "auth_check", None) and callable(authenticated):

        async def by_auth_check() -> bool | None:
            return await authenticated()

        return by_auth_check
    if _is_claude(inner):
        env = getattr(inner, "env", None)

        async def by_claude() -> bool | None:
            return await claude_probe(binary=str(getattr(inner, "executable", "") or "claude"), env=env if isinstance(env, dict) else None)

        return by_claude
    if callable(authenticated):

        async def by_method() -> bool | None:
            return await authenticated()

        return by_method

    async def unknown() -> bool | None:
        return None

    return unknown


def format_wait(seconds: float) -> str:
    seconds = max(0.0, float(seconds))
    if seconds < 90:
        return f"{seconds:.0f} s"
    if seconds < 3600:
        return f"{seconds / 60:.0f} min"
    hours = seconds / 3600
    return f"{hours:g} h" if abs(hours - round(hours)) < 0.05 else f"{hours:.1f} h"


async def wait_for_provider(
    probe: Probe,
    *,
    outage: Outage,
    max_wait_s: float,
    on_wait: Callable[[str], None],
) -> bool:
    """Sleep until the window resets when known, then probe with backoff
    (:data:`BACKOFF_S`, capped) until the provider answers or ``max_wait_s`` is
    spent.  ``on_wait`` gets a one-line status at every step.  A probe that raises is
    an unknown (``None``), never an exception out of the run."""
    started = _now()

    def waited() -> float:
        return _now() - started

    def remaining() -> float:
        return max_wait_s - waited()

    if outage.resume_at is not None:
        delay = min(outage.resume_at + RESET_GRACE_S - _now(), remaining())
        if delay > 0:
            on_wait(
                f"paused: {outage.describe()}; sleeping {format_wait(delay)} until the window resets "
                f"(waited {format_wait(waited())} of {format_wait(max_wait_s)})"
            )
            await _sleep(delay)
    step = 0
    while True:
        try:
            verdict = await probe()
        except Exception as exc:  # noqa: BLE001 -- a broken probe is an unknown, not a crash
            on_wait(f"probe failed ({type(exc).__name__}: {exc}); treating the answer as unknown")
            verdict = None
        if verdict is True or (verdict is None and step >= 1):
            return True
        if remaining() <= 0:
            on_wait(f"gave up waiting for the provider after {format_wait(waited())}: {outage.describe()}")
            return False
        delay = min(BACKOFF_S[min(step, len(BACKOFF_S) - 1)], remaining())
        on_wait(
            f"paused: {outage.describe()}; probing again in {delay:.0f} s "
            f"(waited {format_wait(waited())} of {format_wait(max_wait_s)})"
        )
        await _sleep(delay)
        step += 1


# ------------------------------------------------------------------ the run's one pause


class ProviderPause:
    """One pause per run, shared by every dispatcher (scheduler rounds, the decomposer,
    the approver).  ``hold`` returns ``True`` when the provider came back (retry the
    attempt, uncharged) and ``False`` when the wait was exhausted or the pause is
    disabled (park the node, as before this module existed).  After an exhausted
    wait no later outage pauses again: the run finishes its report.
    """

    def __init__(
        self,
        policy: PausePolicy,
        probe: Probe,
        *,
        on_wait: Callable[[str], None] | None = None,
        on_event: Callable[[str, dict[str, Any]], None] | None = None,
    ) -> None:
        self.policy = policy
        self.probe = probe
        self.on_wait = on_wait
        self.on_event = on_event
        self._resume = asyncio.Event()
        self._resume.set()
        self.current: Outage | None = None
        self.exhausted: Outage | None = None
        self.pauses = 0
        self.waited_s = 0.0
        self.last_wait_s = 0.0
        self._last_resume: float | None = None

    @property
    def enabled(self) -> bool:
        return self.policy.active

    @property
    def paused(self) -> bool:
        return self.current is not None

    async def wait_if_paused(self) -> None:
        """Dispatchers call this before starting anything new; in-flight work never does."""
        await self._resume.wait()

    def _say(self, message: str) -> None:
        if self.on_wait is not None:
            self.on_wait(message)

    def _event(self, kind: str, /, **payload: Any) -> None:
        if self.on_event is not None:
            self.on_event(kind, payload)

    async def hold(self, outage: Outage) -> bool:
        if not self.enabled or not outage.retryable or self.exhausted is not None:
            return False
        if self.current is not None:
            self._event("run.pause_joined", kind=outage.kind, detail=outage.detail)
            await self._resume.wait()
            return self.exhausted is None
        self.current = outage
        self._resume.clear()
        self.pauses += 1
        started = _now()
        self._event("run.paused", kind=outage.kind, detail=outage.detail, resume_at=outage.resume_at, max_wait_s=self.policy.max_wait_s)
        probe = self.probe
        if self._last_resume is not None and started - self._last_resume < REPAUSE_GRACE_S:
            probe = _after_one_backoff(probe)
        ok = False
        try:
            ok = await wait_for_provider(probe, outage=outage, max_wait_s=self.policy.max_wait_s, on_wait=self._say)
        except Exception as exc:  # noqa: BLE001 -- the pause must not become the run's exception
            self._say(f"the pause failed ({type(exc).__name__}: {exc}); treating the wait as exhausted")
            ok = False
        finally:
            self.last_wait_s = _now() - started
            self.waited_s += self.last_wait_s
            self.current = None
            if ok:
                self._last_resume = _now()
            else:
                self.exhausted = outage
            self._resume.set()
        if ok:
            self._event("run.resumed", kind=outage.kind, waited_s=self.last_wait_s)
            self._say(f"resumed after {format_wait(self.last_wait_s)}: the provider answers again")
        else:
            self._event("run.pause_exhausted", kind=outage.kind, detail=outage.detail, waited_s=self.last_wait_s)
        return ok


def _after_one_backoff(probe: Probe) -> Probe:
    """The probe, answering ``False`` once first: forces one backoff sleep."""
    calls = 0

    async def wrapped() -> bool | None:
        nonlocal calls
        calls += 1
        if calls == 1:
            return False
        return await probe()

    return wrapped
