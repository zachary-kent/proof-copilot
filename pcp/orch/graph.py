"""The obligation graph: SQLite, durable, resumable (PLAN.md 8.1, 8.11, 11).

"Own the graph, rent the runner."  This is the part that is specific to the problem,
needs cycles, and must survive process death -- so it is ours, and it is small.

What the store itself guarantees, so that no caller has to remember to:

* every proof-status move goes through :func:`pcp.orch.model.transition` (the
  legacy store accepted ``attic -> integrated``);
* a proof body enters only through :meth:`Graph.record_proof` /
  :meth:`Graph.set_proof_status` with a prover role (:class:`RoleViolation`
  otherwise) -- PLAN.md 8.6's role split is a property of the store, not a prompt;
* a proof invalidation (``gated``/``integrated`` -> ``open``) bumps the epoch and
  clears the body in the same transaction;
* names and ids are unique (a duplicate is a :class:`UsageError`, not an
  ``IntegrityError`` halfway through a plan);
* every mutation is one transaction that also emits its event, so the event log
  never disagrees with the tables after a crash;
* one connection per :class:`Graph`, serialised by a re-entrant lock, so the object
  may be shared across threads (the gate runs in a thread pool);
* the schema is versioned and v1 databases are migrated in place.
"""

from __future__ import annotations

import contextlib
import json
import sqlite3
import threading
import time
from collections.abc import Iterator
from pathlib import Path
from typing import Any

from pcp.errors import RoleViolation, UsageError
from pcp.orch.model import (
    ATTEMPT_STATUSES,
    PROOF_BEARING_ROLES,
    PROOF_STATUSES,
    PROVED_STATUSES,
    RANKS,
    STATEMENT_STATUSES,
    Budget,
    Node,
    node_id,
    transition,
)
from pcp.rocq.body import strip_proof_wrapper
from pcp.rocq.statement import statement_hash
from pcp.util.hashing import content_hash

SCHEMA_VERSION = 2
BUSY_TIMEOUT_S = 30.0

#: v2 DDL.  Every v1 column keeps its name (``tier`` holds the *owner*); v2 adds
#: ``nodes.transparent``, ``attempts.round`` and the unique index on names.
SCHEMA = """
CREATE TABLE IF NOT EXISTS meta (
    key TEXT PRIMARY KEY,
    value TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS nodes (
    id                TEXT PRIMARY KEY,
    name              TEXT NOT NULL,
    rank              TEXT NOT NULL DEFAULT 'local',
    parent            TEXT,
    depth             INTEGER NOT NULL DEFAULT 0,
    epoch             INTEGER NOT NULL DEFAULT 0,
    statement_status  TEXT NOT NULL DEFAULT 'proposed',
    proof_status      TEXT NOT NULL DEFAULT 'open',
    statement         TEXT NOT NULL,
    statement_hash    TEXT NOT NULL,
    closure_hash      TEXT NOT NULL DEFAULT '',
    preamble_hash     TEXT NOT NULL DEFAULT '',
    mockable          INTEGER NOT NULL DEFAULT 1,
    is_glue           INTEGER NOT NULL DEFAULT 0,
    owner             TEXT NOT NULL DEFAULT 'human',
    intent            TEXT NOT NULL DEFAULT '',
    budget            TEXT NOT NULL DEFAULT '{}',
    cost              TEXT NOT NULL DEFAULT '{}',
    attempts          INTEGER NOT NULL DEFAULT 0,
    file              TEXT NOT NULL DEFAULT '',
    body              TEXT,
    evidence          TEXT NOT NULL DEFAULT '',
    ordering          INTEGER NOT NULL DEFAULT 0,
    created_at        REAL NOT NULL,
    updated_at        REAL NOT NULL,
    transparent       INTEGER NOT NULL DEFAULT 0
);
CREATE TABLE IF NOT EXISTS edges (
    src          TEXT NOT NULL,
    dst          TEXT NOT NULL,
    pinned_epoch INTEGER NOT NULL DEFAULT 0,
    kind         TEXT NOT NULL DEFAULT 'uses',
    PRIMARY KEY (src, dst, kind),
    FOREIGN KEY (src) REFERENCES nodes(id) ON DELETE CASCADE,
    FOREIGN KEY (dst) REFERENCES nodes(id) ON DELETE CASCADE
);
CREATE TABLE IF NOT EXISTS attempts (
    id        INTEGER PRIMARY KEY AUTOINCREMENT,
    node      TEXT NOT NULL,
    epoch     INTEGER NOT NULL,
    runner    TEXT NOT NULL DEFAULT '',
    tier      TEXT NOT NULL DEFAULT '',
    role      TEXT NOT NULL DEFAULT 'prover',
    model     TEXT NOT NULL DEFAULT '',
    started   REAL NOT NULL,
    finished  REAL,
    status    TEXT NOT NULL DEFAULT 'claimed',
    evidence  TEXT NOT NULL DEFAULT '',
    requests  TEXT NOT NULL DEFAULT '[]',
    body      TEXT,
    gate      TEXT NOT NULL DEFAULT '{}',
    cost      TEXT NOT NULL DEFAULT '{}',
    round     INTEGER NOT NULL DEFAULT 1,
    FOREIGN KEY (node) REFERENCES nodes(id) ON DELETE CASCADE
);
CREATE TABLE IF NOT EXISTS events (
    id      INTEGER PRIMARY KEY AUTOINCREMENT,
    ts      REAL NOT NULL,
    node    TEXT,
    kind    TEXT NOT NULL,
    payload TEXT NOT NULL DEFAULT '{}'
);
CREATE TABLE IF NOT EXISTS blobs (
    hash    TEXT PRIMARY KEY,
    content BLOB NOT NULL
);
CREATE TABLE IF NOT EXISTS amendments (
    id         INTEGER PRIMARY KEY AUTOINCREMENT,
    node       TEXT NOT NULL,
    from_epoch INTEGER NOT NULL,
    to_epoch   INTEGER NOT NULL,
    klass      TEXT NOT NULL,
    status     TEXT NOT NULL DEFAULT 'proposed',
    rationale  TEXT NOT NULL DEFAULT '',
    evidence   TEXT NOT NULL DEFAULT '',
    impact     TEXT NOT NULL DEFAULT '{}',
    statement  TEXT NOT NULL DEFAULT '',
    created_at REAL NOT NULL,
    FOREIGN KEY (node) REFERENCES nodes(id) ON DELETE CASCADE
);
CREATE INDEX IF NOT EXISTS idx_nodes_proof   ON nodes(proof_status);
CREATE INDEX IF NOT EXISTS idx_nodes_parent  ON nodes(parent);
CREATE UNIQUE INDEX IF NOT EXISTS idx_nodes_name ON nodes(name);
CREATE INDEX IF NOT EXISTS idx_edges_dst     ON edges(dst);
CREATE INDEX IF NOT EXISTS idx_events_ts     ON events(ts);
CREATE INDEX IF NOT EXISTS idx_attempts_node ON attempts(node);
"""

NODE_COLUMNS: tuple[str, ...] = (
    "id", "name", "rank", "parent", "depth", "epoch", "statement_status", "proof_status",
    "statement", "statement_hash", "closure_hash", "preamble_hash", "mockable", "is_glue",
    "owner", "intent", "budget", "cost", "attempts", "file", "body", "evidence", "ordering",
    "created_at", "updated_at", "transparent",
)
_BOOL_COLUMNS = ("mockable", "is_glue", "transparent")
_JSON_COLUMNS = ("cost",)
#: The statement ledger.  Only a human write (a plan, a design round, an amendment)
#: may restate an obligation or move its epoch: a prover attempt that could rewrite
#: its own statement through ``update()`` would be stating, not proving (PLAN.md 8.6).
_HUMAN_ONLY_COLUMNS = ("statement", "statement_hash", "statement_status", "epoch")


def _row_to_node(row: sqlite3.Row) -> Node:
    keys = set(row.keys())
    return Node(
        id=row["id"],
        name=row["name"],
        statement=row["statement"],
        statement_hash=row["statement_hash"],
        rank=row["rank"],
        parent=row["parent"],
        depth=row["depth"],
        epoch=row["epoch"],
        statement_status=row["statement_status"],
        proof_status=row["proof_status"],
        closure_hash=row["closure_hash"],
        preamble_hash=row["preamble_hash"],
        mockable=bool(row["mockable"]),
        # Absent on a v1 database opened read-only (no migration is possible there).
        transparent=bool(row["transparent"]) if "transparent" in keys else False,
        is_glue=bool(row["is_glue"]),
        owner=row["owner"],
        intent=row["intent"],
        budget=Budget.from_json(row["budget"]),
        cost=json.loads(row["cost"] or "{}"),
        attempts=row["attempts"],
        file=row["file"],
        body=row["body"],
        evidence=row["evidence"],
        ordering=row["ordering"],
        created_at=row["created_at"],
        updated_at=row["updated_at"],
    )


class Graph:
    """The durable obligation graph.  Every mutation is one transaction and one event."""

    def __init__(self, path: str | Path, *, _readonly: bool = False) -> None:
        self.path = Path(path)
        self.readonly = _readonly
        self._lock = threading.RLock()
        self._depth = 0
        if _readonly:
            if not self.path.exists():
                raise UsageError(f"no graph at {self.path}")
            self.db = sqlite3.connect(
                f"file:{self.path}?mode=ro", uri=True, check_same_thread=False, timeout=BUSY_TIMEOUT_S,
                isolation_level=None,
            )
            self.db.row_factory = sqlite3.Row
            return
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.db = sqlite3.connect(
            str(self.path), check_same_thread=False, timeout=BUSY_TIMEOUT_S, isolation_level=None
        )
        self.db.row_factory = sqlite3.Row
        self.db.execute("PRAGMA journal_mode=WAL")
        self.db.execute("PRAGMA foreign_keys=ON")
        self.db.execute(f"PRAGMA busy_timeout={int(BUSY_TIMEOUT_S * 1000)}")
        self._ensure_schema()

    @classmethod
    def open_readonly(cls, path: str | Path) -> Graph:
        """Open an existing graph without creating or writing anything.

        ``pcp status``/``handoff``/``report`` used to create an empty database when
        given a wrong path and then resume from it; the ``mode=ro`` URI makes that
        impossible.
        """
        return cls(path, _readonly=True)

    # -- schema ------------------------------------------------------------
    def _ensure_schema(self) -> None:
        # ``executescript`` commits on its own, so DDL runs outside :meth:`_tx`.
        with self._lock:
            has_nodes = self.db.execute(
                "SELECT 1 FROM sqlite_master WHERE type='table' AND name='nodes'"
            ).fetchone()
            if not has_nodes:
                self.db.executescript(SCHEMA)
                with self._tx():
                    self._set_meta("schema_version", str(SCHEMA_VERSION))
                return
            version = int(self.get_meta("schema_version", "1") or "1")
            if version > SCHEMA_VERSION:
                raise UsageError(
                    f"{self.path} has schema version {version}, newer than this tool ({SCHEMA_VERSION})"
                )
            if version < SCHEMA_VERSION:
                self._migrate(version)

    def _migrate(self, from_version: int) -> None:
        """v1 -> v2: add the new columns, require unique names, record the version."""
        dupes = [
            r[0] for r in self.db.execute("SELECT name FROM nodes GROUP BY name HAVING COUNT(*) > 1")
        ]
        if dupes:
            raise UsageError(
                f"{self.path}: cannot migrate, node names are not unique: {', '.join(dupes)}; "
                "start over with --fresh"
            )
        node_cols = {r[1] for r in self.db.execute("PRAGMA table_info(nodes)")}
        attempt_cols = {r[1] for r in self.db.execute("PRAGMA table_info(attempts)")}
        if "transparent" not in node_cols:
            self.db.execute("ALTER TABLE nodes ADD COLUMN transparent INTEGER NOT NULL DEFAULT 0")
        if "round" not in attempt_cols:
            self.db.execute("ALTER TABLE attempts ADD COLUMN round INTEGER NOT NULL DEFAULT 1")
        self.db.executescript(SCHEMA)  # idempotent: creates whatever else is missing
        with self._tx():
            self._set_meta("schema_version", str(SCHEMA_VERSION))
            self._emit("schema.migrated", None, from_version=from_version, to_version=SCHEMA_VERSION)

    # -- transactions ------------------------------------------------------
    @contextlib.contextmanager
    def _tx(self) -> Iterator[None]:
        """One write transaction, however deeply the public methods nest."""
        with self._lock:
            if self.readonly:
                raise UsageError(f"{self.path} was opened read-only")
            self._depth += 1
            try:
                if self._depth == 1:
                    self.db.execute("BEGIN IMMEDIATE")
                yield
            except BaseException:
                if self._depth == 1:
                    self.db.execute("ROLLBACK")
                raise
            else:
                if self._depth == 1:
                    self.db.execute("COMMIT")
            finally:
                self._depth -= 1

    @contextlib.contextmanager
    def transaction(self) -> Iterator[None]:
        """Group several mutations into one commit.

        Integration's N+1 status writes and a plan adoption are one decision each;
        a crash halfway through must leave none of them (audit: "no multi-row
        transition is atomic").  Every public method nests inside this.
        """
        with self._tx():
            yield

    # -- meta / blobs ------------------------------------------------------
    def _set_meta(self, key: str, value: str) -> None:
        self.db.execute(
            "INSERT INTO meta(key, value) VALUES(?, ?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
            (key, value),
        )

    def set_meta(self, key: str, value: str) -> None:
        with self._tx():
            self._set_meta(key, value)
            self._emit("meta.set", None, key=key, value=value[:400])

    def get_meta(self, key: str, default: str | None = None) -> str | None:
        with self._lock:
            row = self.db.execute("SELECT value FROM meta WHERE key=?", (key,)).fetchone()
        return row["value"] if row else default

    def delete_meta(self, key: str) -> bool:
        """Forget a meta key (e.g. a once-per-epoch adjudication marker, to re-ask)."""
        with self._lock, self.db:
            cur = self.db.execute("DELETE FROM meta WHERE key=?", (key,))
        removed = cur.rowcount > 0
        if removed:
            self._emit("meta.deleted", None, key=key)
        return removed

    def put_blob(self, content: str) -> str:
        h = content_hash(content)
        with self._tx():
            self.db.execute(
                "INSERT INTO blobs(hash, content) VALUES(?, ?) ON CONFLICT(hash) DO NOTHING",
                (h, content.encode("utf-8")),
            )
            self._emit("blob.put", None, hash=h, size=len(content))
        return h

    def get_blob(self, h: str) -> str | None:
        with self._lock:
            row = self.db.execute("SELECT content FROM blobs WHERE hash=?", (h,)).fetchone()
        return row["content"].decode("utf-8") if row else None

    # -- events ------------------------------------------------------------
    def _emit(self, kind: str, node: str | None, /, **payload: Any) -> int:
        cur = self.db.execute(
            "INSERT INTO events(ts, node, kind, payload) VALUES(?, ?, ?, ?)",
            (time.time(), node, kind, json.dumps(payload, default=str)),
        )
        return int(cur.lastrowid or 0)

    def emit(self, kind: str, node: str | None = None, /, **payload: Any) -> int:
        with self._tx():
            return self._emit(kind, node, **payload)

    def events_since(self, event_id: int = 0, limit: int = 500) -> list[dict[str, Any]]:
        with self._lock:
            rows = self.db.execute(
                "SELECT id, ts, node, kind, payload FROM events WHERE id > ? ORDER BY id LIMIT ?",
                (event_id, limit),
            ).fetchall()
        return [
            {"id": r["id"], "ts": r["ts"], "node": r["node"], "kind": r["kind"], "payload": json.loads(r["payload"])}
            for r in rows
        ]

    # -- nodes -------------------------------------------------------------
    def add_node(self, node: Node) -> Node:
        if not node.id:
            node.id = node_id(node.name)
        if not node.name:
            raise UsageError("a node needs a name")
        if node.rank not in RANKS:
            raise UsageError(f"node {node.name!r}: unknown rank {node.rank!r}; one of {', '.join(RANKS)}")
        if node.statement_status not in STATEMENT_STATUSES:
            raise UsageError(f"node {node.name!r}: unknown statement status {node.statement_status!r}")
        if node.proof_status not in PROOF_STATUSES:
            raise UsageError(f"node {node.name!r}: unknown proof status {node.proof_status!r}")
        if node.body is not None:
            node.body = strip_proof_wrapper(node.body)
        now = time.time()
        node.created_at = node.created_at or now
        node.updated_at = now
        if not node.statement_hash:
            node.statement_hash = statement_hash(node.statement)
        with self._tx():
            if self._get(node.id) is not None:
                raise UsageError(f"a node with id {node.id!r} already exists (name {node.name!r})")
            if self._by_name(node.name) is not None:
                raise UsageError(f"a node named {node.name!r} already exists")
            self.db.execute(
                """INSERT INTO nodes(id, name, rank, parent, depth, epoch, statement_status, proof_status,
                                     statement, statement_hash, closure_hash, preamble_hash, mockable, is_glue,
                                     owner, intent, budget, cost, attempts, file, body, evidence, ordering,
                                     created_at, updated_at, transparent)
                   VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
                (
                    node.id, node.name, node.rank, node.parent, node.depth, node.epoch,
                    node.statement_status, node.proof_status, node.statement, node.statement_hash,
                    node.closure_hash, node.preamble_hash, int(node.mockable), int(node.is_glue),
                    node.owner, node.intent, node.budget.dumps(), json.dumps(node.cost),
                    node.attempts, node.file, node.body, node.evidence, node.ordering,
                    node.created_at, node.updated_at, int(node.transparent),
                ),
            )
            self._emit("node.added", node.id, name=node.name, rank=node.rank, parent=node.parent)
        return node

    def _get(self, node_id_: str) -> Node | None:
        row = self.db.execute("SELECT * FROM nodes WHERE id=?", (node_id_,)).fetchone()
        return _row_to_node(row) if row else None

    def _by_name(self, name: str) -> Node | None:
        row = self.db.execute("SELECT * FROM nodes WHERE name=?", (name,)).fetchone()
        return _row_to_node(row) if row else None

    def get(self, node_id_: str) -> Node | None:
        with self._lock:
            return self._get(node_id_)

    def require(self, node_id_: str) -> Node:
        node = self.get(node_id_)
        if node is None:
            raise UsageError(f"no node {node_id_!r} in {self.path}")
        return node

    def by_name(self, name: str) -> Node | None:
        with self._lock:
            return self._by_name(name)

    def nodes(self, **where: Any) -> list[Node]:
        for key in where:
            if key not in NODE_COLUMNS:
                raise UsageError(f"nodes(): unknown column {key!r}")
        clause = " AND ".join(f"{k}=?" for k in where)
        sql = "SELECT * FROM nodes" + (f" WHERE {clause}" if clause else "") + " ORDER BY ordering, created_at"
        values = tuple(int(v) if k in _BOOL_COLUMNS else v for k, v in where.items())
        with self._lock:
            return [_row_to_node(r) for r in self.db.execute(sql, values).fetchall()]

    def update(self, node_id_: str, *, role: str = "prover", **fields: Any) -> Node:
        """Generic column update with the store's invariants enforced.

        A non-``None`` ``body`` is refused here for every role: proofs enter through
        :meth:`record_proof`.  A ``proof_status`` change is validated by
        :func:`transition`; an invalidating move also bumps ``epoch`` and clears the
        body.
        """
        if "body" in fields and fields["body"] is not None:
            raise RoleViolation(
                f"refusing to attach a proof to {node_id_!r} through update(): "
                "only a prover attempt may put proof text into the graph (record_proof)"
            )
        return self._update(node_id_, fields, role=role)

    def _update(self, node_id_: str, fields: dict[str, Any], *, role: str) -> Node:
        for key in fields:
            if key not in NODE_COLUMNS or key in ("id", "created_at"):
                raise UsageError(f"update(): unknown or immutable column {key!r}")
        if "rank" in fields and fields["rank"] not in RANKS:
            raise UsageError(f"unknown rank {fields['rank']!r}")
        if "statement_status" in fields and fields["statement_status"] not in STATEMENT_STATUSES:
            raise UsageError(f"unknown statement status {fields['statement_status']!r}")
        restated = [k for k in _HUMAN_ONLY_COLUMNS if k in fields]
        if restated and role != "human":
            raise RoleViolation(
                f"role {role!r} may not change {', '.join(restated)} of {node_id_!r}: "
                "only a human write restates an obligation or moves its epoch"
            )
        with self._tx():
            node = self._get(node_id_)
            if node is None:
                raise UsageError(f"no node {node_id_!r} in {self.path}")
            if "proof_status" in fields and fields["proof_status"] != node.proof_status:
                new = fields["proof_status"]
                transition(node.proof_status, new, proved=node.proved, human=role == "human")
                if (node.proof_status, new) in _invalidating() and "epoch" not in fields:
                    fields["epoch"] = node.epoch + 1
                if (node.proof_status, new) in _invalidating():
                    fields.setdefault("body", None)
            if "budget" in fields and isinstance(fields["budget"], Budget):
                fields["budget"] = fields["budget"].dumps()
            for key in _JSON_COLUMNS:
                if key in fields and isinstance(fields[key], dict):
                    fields[key] = json.dumps(fields[key], default=str)
            for key in _BOOL_COLUMNS:
                if key in fields:
                    fields[key] = int(bool(fields[key]))
            if not fields:
                return node
            fields["updated_at"] = time.time()
            sets = ", ".join(f"{k}=?" for k in fields)
            self.db.execute(f"UPDATE nodes SET {sets} WHERE id=?", (*fields.values(), node_id_))
            changed = {k: v for k, v in fields.items() if k not in ("updated_at", "body", "evidence")}
            if "body" in fields:
                changed["body"] = "cleared" if fields["body"] is None else "set"
            if "evidence" in fields:
                changed["evidence"] = str(fields["evidence"])[:400]
            self._emit("node.updated", node_id_, role=role, **changed)
            updated = self._get(node_id_)
            assert updated is not None
            return updated

    def set_proof_status(
        self,
        node_id_: str,
        status: str,
        *,
        evidence: str = "",
        body: str | None = None,
        role: str = "prover",
    ) -> Node:
        if status not in PROOF_STATUSES:
            raise UsageError(f"unknown proof status {status!r}; one of {', '.join(PROOF_STATUSES)}")
        fields: dict[str, Any] = {"proof_status": status}
        if evidence:
            fields["evidence"] = evidence
        if body is not None:
            if role not in PROOF_BEARING_ROLES:
                raise RoleViolation(
                    f"role {role!r} may not attach a proof to {node_id_!r}; "
                    "decomposers state obligations, provers prove them"
                )
            fields["body"] = strip_proof_wrapper(body)
        with self._tx():
            node = self._update(node_id_, fields, role=role)
            self._emit("node.proof_status", node_id_, status=status, evidence=evidence[:400], role=role)
        return node

    def record_proof(self, node_id_: str, body: str, *, role: str = "prover", status: str = "gated") -> Node:
        """The only way a proof reaches the graph (wrapper ``Proof.``/``Qed.`` stripped)."""
        return self.set_proof_status(node_id_, status, body=body, role=role)

    def clear_body(self, node_id_: str, *, role: str = "prover") -> Node:
        """Drop a node's body -- what a proof invalidation does, callable on its own."""
        with self._tx():
            node = self._update(node_id_, {"body": None}, role=role)
            self._emit("node.body_cleared", node_id_, role=role)
        return node

    def freeze(self, node_id_: str, *, closure_hash: str = "", preamble_hash: str = "") -> Node:
        fields: dict[str, Any] = {"statement_status": "frozen"}
        if closure_hash:
            fields["closure_hash"] = closure_hash
        if preamble_hash:
            fields["preamble_hash"] = preamble_hash
        with self._tx():
            node = self._update(node_id_, fields, role="human")
            self._emit("node.frozen", node_id_, epoch=node.epoch)
        return node

    # -- edges -------------------------------------------------------------
    def add_edge(self, src: str, dst: str, *, kind: str = "uses", pinned_epoch: int | None = None) -> None:
        """``src``'s proof references ``dst``, pinned to ``dst``'s current epoch.

        The pin is what makes staleness pure graph arithmetic: a proof is always of a
        specific statement epoch, and integration requires every edge to be current.
        """
        with self._tx():
            target = self._get(dst)
            if target is None or self._get(src) is None:
                raise UsageError(f"add_edge({src!r}, {dst!r}): both nodes must exist")
            if pinned_epoch is None:
                pinned_epoch = target.epoch
            self.db.execute(
                "INSERT INTO edges(src, dst, pinned_epoch, kind) VALUES(?,?,?,?) "
                "ON CONFLICT(src, dst, kind) DO UPDATE SET pinned_epoch=excluded.pinned_epoch",
                (src, dst, pinned_epoch, kind),
            )
            self._emit("edge.added", src, dst=dst, kind=kind, pinned_epoch=pinned_epoch)

    def deps(self, node_id_: str) -> list[tuple[str, int, str]]:
        with self._lock:
            rows = self.db.execute("SELECT dst, pinned_epoch, kind FROM edges WHERE src=?", (node_id_,)).fetchall()
        return [(r["dst"], r["pinned_epoch"], r["kind"]) for r in rows]

    def dependents(self, node_id_: str) -> list[str]:
        with self._lock:
            rows = self.db.execute("SELECT src FROM edges WHERE dst=?", (node_id_,)).fetchall()
        return [r["src"] for r in rows]

    def stale_edges(self, node_id_: str) -> list[tuple[str, int, int]]:
        """Edges whose pinned epoch is behind the dependency's current epoch."""
        out = []
        with self._lock:
            for dst, pinned, _kind in self.deps(node_id_):
                target = self._get(dst)
                if target and target.epoch != pinned:
                    out.append((dst, pinned, target.epoch))
        return out

    def transitive_dependents(self, node_id_: str) -> list[str]:
        seen: set[str] = set()
        stack = [node_id_]
        with self._lock:
            while stack:
                cur = stack.pop()
                for src in self.dependents(cur):
                    if src not in seen:
                        seen.add(src)
                        stack.append(src)
        return sorted(seen)

    # -- scheduling --------------------------------------------------------
    def frontier(self) -> list[Node]:
        """Every dispatchable node, non-mockable first, shallower first, plan order."""
        nodes = [n for n in self.nodes() if n.dispatchable]
        return sorted(nodes, key=lambda n: (n.mockable, n.depth, n.ordering))

    def open_count(self) -> int:
        return len([n for n in self.nodes() if n.proof_status == "open"])

    def summary(self) -> dict[str, int]:
        counts: dict[str, int] = {}
        for n in self.nodes():
            counts[n.proof_status] = counts.get(n.proof_status, 0) + 1
        return counts

    # -- attempts ----------------------------------------------------------
    def start_attempt(
        self, node_id_: str, *, runner: str = "", owner: str = "", role: str = "prover", round: int = 1
    ) -> int:
        """Record the start of one attempt and return its (globally unique) id.

        ``owner`` is who *stated* the obligation (stored in the legacy ``tier``
        column); ``runner``/``role``/``model`` say who ran it.  Only prover attempts
        count towards ``nodes.attempts``: a decomposer round on the root is not a
        proof attempt, and reporting it as one misattributed effort in every status.
        """
        with self._tx():
            node = self._get(node_id_)
            if node is None:
                raise UsageError(f"no node {node_id_!r} in {self.path}")
            now = time.time()
            cur = self.db.execute(
                "INSERT INTO attempts(node, epoch, runner, tier, role, started, status, round) "
                "VALUES(?,?,?,?,?,?,?,?)",
                (node_id_, node.epoch, runner, owner or node.owner, role, now, "claimed", int(round)),
            )
            attempt_id = int(cur.lastrowid or 0)
            if role in PROOF_BEARING_ROLES:
                self.db.execute(
                    "UPDATE nodes SET attempts = attempts + 1, updated_at=? WHERE id=?", (now, node_id_)
                )
            self._emit(
                "attempt.started", node_id_, runner=runner, owner=owner or node.owner, role=role,
                attempt=attempt_id, round=int(round),
            )
        return attempt_id

    def finish_attempt(
        self,
        attempt_id: int,
        *,
        status: str,
        evidence: str = "",
        body: str | None = None,
        gate: dict[str, Any] | None = None,
        cost: dict[str, Any] | None = None,
        requests: list[dict[str, Any]] | None = None,
        model: str = "",
    ) -> None:
        """Close an attempt row.  ``model`` is the *resolved* model, not the runner's label."""
        if status not in ATTEMPT_STATUSES or status == "claimed":
            raise UsageError(f"finish_attempt: unknown status {status!r}")
        with self._tx():
            row = self.db.execute("SELECT node FROM attempts WHERE id=?", (attempt_id,)).fetchone()
            if row is None:
                raise UsageError(f"no attempt {attempt_id} in {self.path}")
            self.db.execute(
                "UPDATE attempts SET finished=?, status=?, evidence=?, body=?, gate=?, cost=?, "
                "requests=?, model=? WHERE id=?",
                (
                    time.time(), status, evidence, body,
                    json.dumps(gate or {}, default=str), json.dumps(cost or {}, default=str),
                    json.dumps(requests or [], default=str), model, attempt_id,
                ),
            )
            self._emit("attempt.finished", row["node"], status=status, attempt=attempt_id, model=model)

    def attempt(self, attempt_id: int) -> dict[str, Any] | None:
        with self._lock:
            row = self.db.execute("SELECT * FROM attempts WHERE id=?", (attempt_id,)).fetchone()
        return dict(row) if row else None

    def attempts_for(self, node_id_: str) -> list[dict[str, Any]]:
        """Raw attempt rows, oldest first (``gate``/``cost``/``requests`` are JSON text)."""
        with self._lock:
            rows = self.db.execute("SELECT * FROM attempts WHERE node=? ORDER BY id", (node_id_,)).fetchall()
        return [dict(r) for r in rows]

    def salvageable_body(self, node_id_: str, *, epoch: int | None = None) -> str | None:
        """The latest gated body an attempt left behind -- for crash resume.

        A run killed between ``finish_attempt`` and ``set_proof_status`` has a proof
        the gate accepted and a node that still says ``claimed``; this finds it.

        Only attempts at the node's **current** statement epoch count (or ``epoch``
        when given): a body gated against an earlier statement is not a proof of the
        current one, and salvaging it re-injected an invalidated proof as a proved
        sibling (review finding).
        """
        node = self.get(node_id_)
        wanted = epoch if epoch is not None else (node.epoch if node else 0)
        for row in reversed(self.attempts_for(node_id_)):
            if row.get("status") != "qed" or not row.get("body"):
                continue
            if int(row.get("epoch") or 0) != wanted:
                continue
            try:
                gate = json.loads(row.get("gate") or "{}")
            except json.JSONDecodeError:
                continue
            if isinstance(gate, dict) and gate.get("ok") is True:
                return str(row["body"])
        return None

    # -- lifecycle ---------------------------------------------------------
    def close(self) -> None:
        with self._lock:
            self.db.close()

    def __enter__(self) -> Graph:
        return self

    def __exit__(self, *exc: object) -> None:
        self.close()


def _invalidating() -> frozenset[tuple[str, str]]:
    from pcp.orch.model import INVALIDATING_MOVES

    return INVALIDATING_MOVES


__all__ = ["SCHEMA_VERSION", "Graph", "Node", "Budget", "PROVED_STATUSES"]
