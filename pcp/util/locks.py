"""A run lock, so two ``pcp prove`` invocations cannot share one graph (PLAN.md 8.11).

The lock is an advisory ``flock`` on ``<graph>.lock``; the file records the holder's
pid and start time so the message a second run sees is actionable.
"""

from __future__ import annotations

import fcntl
import json
import os
import time
from pathlib import Path
from types import TracebackType
from typing import IO

from pcp.errors import LockedError


class RunLock:
    def __init__(self, path: str | Path) -> None:
        self.path = Path(path)
        self._fh: IO[str] | None = None

    def acquire(self) -> RunLock:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        fh = open(self.path, "a+", encoding="utf-8")
        try:
            fcntl.flock(fh.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            fh.seek(0)
            holder = fh.read().strip()
            fh.close()
            raise LockedError(
                f"another pcp run holds {self.path} ({holder or 'holder unknown'}); "
                "wait for it, or point this run at a different --graph"
            ) from None
        fh.seek(0)
        fh.truncate()
        fh.write(json.dumps({"pid": os.getpid(), "started_at": time.time()}))
        fh.flush()
        self._fh = fh
        return self

    def release(self) -> None:
        if self._fh is None:
            return
        try:
            fcntl.flock(self._fh.fileno(), fcntl.LOCK_UN)
        finally:
            self._fh.close()
            self._fh = None

    def __enter__(self) -> RunLock:
        return self.acquire()

    def __exit__(self, exc_type: type[BaseException] | None, exc: BaseException | None, tb: TracebackType | None) -> None:
        self.release()
