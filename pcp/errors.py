"""The error hierarchy.  Only ``pcp.cli.main`` turns these into exit codes.

Every error carries a one-line, user-facing message.  Library code raises; it never
prints and never calls ``SystemExit``.
"""

from __future__ import annotations


class PcpError(Exception):
    """Base class.  ``exit_code`` is what the CLI returns for it."""

    exit_code = 1

    def __init__(self, message: str) -> None:
        super().__init__(message)
        self.message = message

    def __str__(self) -> str:
        return self.message


class UsageError(PcpError):
    """Bad arguments, missing files, malformed plans -- the operator's to fix."""

    exit_code = 2


class ToolchainError(PcpError):
    """A required binary or library is missing or broken (coqc, pet, bwrap, claude)."""

    exit_code = 1


class ProtocolError(PcpError):
    """A worker, decomposer or provider broke the protocol (malformed answer, bad stream)."""


class GateError(PcpError):
    """The gate could not run at all (as opposed to a failed check, which is a result)."""


class RoleViolation(PcpError):
    """Something that is not a prover tried to put a proof into the graph (PLAN.md 8.6)."""


class StateError(PcpError):
    """The petanque state layer lost or refused a session/state."""


class LockedError(PcpError):
    """Another ``pcp prove`` holds the run lock on this graph."""

    exit_code = 2
