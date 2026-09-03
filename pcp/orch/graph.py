"""The obligation graph: SQLite, durable, resumable (PLAN.md 8.1, 11).

"Own the graph, rent the runner."  This is the part that is specific to the problem,
needs cycles, and must survive process death -- so it is ours, and it is small.
Everything below it (running one node attempt) is commodity behind ``Runner``.

Two ledgers per node, because statements and proofs have separate lifecycles::

    statement:  proposed → audited → frozen@e ──amend──▶ frozen@e+1
                                        └────────────▶ refuted   (terminal)
    proof:      open → claimed → qed → gated → integrated        (per epoch)
                          └──▶ contested(evidence) | stuck(evidence, requests)

The scheduling invariant that makes the whole design work: **every statement
``frozen@e`` with an ``open`` proof is dispatchable now**, because its dependencies'
statements are frozen and admissible as stubs.  Edges are for invalidation, assembly
and axiom accounting -- not for readiness.
"""

from __future__ import annotations

import json
import sqlite3
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

SCHEMA_VERSION = 1

StatementStatus = ("proposed", "audited", "frozen", "refuted")
ProofStatus = ("open", "claimed", "qed", "gated", "integrated", "contested", "stuck", "attic")
Rank = ("root", "interface", "local")

#: Roles that may attach proof text.  Exactly one, on purpose (PLAN.md 8.6).
PROOF_BEARING_ROLES = ("prover",)

SCHEMA = """
PRAGMA journal_mode=WAL;
PRAGMA foreign_keys=ON;

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
    updated_at        REAL NOT NULL
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
CREATE INDEX IF NOT EXISTS idx_edges_dst     ON edges(dst);
CREATE INDEX IF NOT EXISTS idx_events_ts     ON events(ts);
CREATE INDEX IF NOT EXISTS idx_attempts_node ON attempts(node);
"""


@dataclass
class Budget:
    """Budgets are **vectors, denominated per provider** (PLAN.md 11, Economics).

    A flat-rate subscription's capacity is requests per window and its marginal token
    cost is ~0; a metered API's is dollars.  Mixing them into one scalar is how you
    end up throttling the free tier to protect a budget it does not spend.
    """

    requests: int = 0
    tokens: int = 0
    dollars: float = 0.0
    seconds: float = 0.0

    def split(self, n: int, *, share: float = 1.0) -> "Budget":
        """Divide the metered dimensions among ``n`` siblings -- but not the clock.

        Requests, tokens and dollars are consumed from one pool, so splitting them is
        what keeps ``n`` children inside the parent's allowance. **Wall-clock is not
        that kind of resource**: children are dispatched concurrently
        (`Scheduler.run` gathers them), so a second spent by one is not a second
        denied to another, and dividing gives every child the *same* deadline whether
        it is a one-line arithmetic lemma or the hardest obligation in the plan.

        Measured on seqlock_wf: a 7200 s root split six ways gave each child 1200 s.
        Four finished in 78 s, 479 s, 522 s and 983 s; the other two were killed at
        the deadline with 2738 s of their siblings' allowance never spent -- and both
        were the run's only unproved obligations. `share` still scales the clock,
        because "use a fraction of the parent's time" is a real instruction; `/n` is
        not.
        """
        n = max(1, n)
        return Budget(
            requests=int(self.requests * share) // n,
            tokens=int(self.tokens * share) // n,
            dollars=self.dollars * share / n,
            seconds=self.seconds * share,
        )

    @property
    def unset(self) -> bool:
        """No budget configured at all.

        An all-zero vector means "nobody set a budget", not "the budget is spent".
        Conflating the two makes an unconfigured node look exhausted, which silently
        blocks every decomposition -- a failure that is invisible until nothing
        dispatches.
        """
        return self.requests == 0 and self.tokens == 0 and self.dollars == 0.0 and self.seconds == 0.0

    def exhausted(self) -> bool:
        if self.unset:
            return False
        return self.requests <= 0 and self.tokens <= 0 and self.dollars <= 0.0

    def to_json(self) -> str:
        return json.dumps(asdict(self))

    @classmethod
    def from_json(cls, text: str | None) -> "Budget":
        if not text:
            return cls()
        try:
            return cls(**json.loads(text))
        except (json.JSONDecodeError, TypeError):
            return cls()


@dataclass
class Node:
    id: str
    name: str
    statement: str
    statement_hash: str = ""
    rank: str = "local"
    parent: str | None = None
    depth: int = 0
    epoch: int = 0
    statement_status: str = "proposed"
    proof_status: str = "open"
    closure_hash: str = ""
    preamble_hash: str = ""
    mockable: bool = True
    is_glue: bool = False
    owner: str = "human"
    intent: str = ""
    budget: Budget = field(default_factory=Budget)
    cost: dict[str, Any] = field(default_factory=dict)
    attempts: int = 0
    file: str = ""
    body: str | None = None
    evidence: str = ""
    ordering: int = 0
    created_at: float = 0.0
    updated_at: float = 0.0

    @property
    def frozen(self) -> bool:
        return self.statement_status == "frozen"

    @property
    def dispatchable(self) -> bool:
        """The scheduling invariant, in one line.

        A frozen statement with an open proof is dispatchable *now* -- its
        dependencies are admissible as stubs, so graph depth never gates dispatch.
        """
        return self.frozen and self.proof_status == "open"

    @property
    def done(self) -> bool:
        return self.proof_status in ("gated", "integrated")


def _row_to_node(row: sqlite3.Row) -> Node:
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


class RoleViolation(RuntimeError):
    """Something that is not a prover tried to put a proof into the graph.

    PLAN.md 8.6 gives the roles disjoint jobs: decomposers own *statements*, provers
    own *proofs*, and the gate is not a model at all.  Enforcing that by instruction
    would leave it to the same model whose incentive is to shortcut it, so the graph
    refuses the write instead.
    """


class Graph:
    """The durable obligation graph.  Every mutation is an event, for the dashboard."""

    def __init__(self, path: str | Path = ".pcp/graph.db") -> None:
        self.path = Path(path)
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.db = sqlite3.connect(str(self.path), check_same_thread=False, timeout=30.0)
        self.db.row_factory = sqlite3.Row
        self.db.executescript(SCHEMA)
        self.set_meta("schema_version", str(SCHEMA_VERSION))
        self.db.commit()
        #: Raised to True only inside :meth:`record_proof`.  Every other path that
        #: tries to write a `body` is refused, so "the orchestrator does no proof
        #: engineering" is a property of the store rather than of a prompt.
        self._proof_write_allowed = False

    # -- meta / blobs ------------------------------------------------------
    def set_meta(self, key: str, value: str) -> None:
        self.db.execute(
            "INSERT INTO meta(key, value) VALUES(?, ?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
            (key, value),
        )
        self.db.commit()

    def get_meta(self, key: str, default: str | None = None) -> str | None:
        row = self.db.execute("SELECT value FROM meta WHERE key=?", (key,)).fetchone()
        return row["value"] if row else default

    def put_blob(self, content: str) -> str:
        from pcp.orch.hashing import content_hash

        h = content_hash(content)
        self.db.execute(
            "INSERT INTO blobs(hash, content) VALUES(?, ?) ON CONFLICT(hash) DO NOTHING",
            (h, content.encode("utf-8")),
        )
        self.db.commit()
        return h

    def get_blob(self, h: str) -> str | None:
        row = self.db.execute("SELECT content FROM blobs WHERE hash=?", (h,)).fetchone()
        return row["content"].decode("utf-8") if row else None

    # -- events ------------------------------------------------------------
    def emit(self, kind: str, node: str | None = None, **payload: Any) -> int:
        cur = self.db.execute(
            "INSERT INTO events(ts, node, kind, payload) VALUES(?, ?, ?, ?)",
            (time.time(), node, kind, json.dumps(payload, default=str)),
        )
        self.db.commit()
        return int(cur.lastrowid or 0)

    def events_since(self, event_id: int = 0, limit: int = 500) -> list[dict[str, Any]]:
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
        now = time.time()
        node.created_at = node.created_at or now
        node.updated_at = now
        if not node.statement_hash:
            from pcp.orch.hashing import statement_hash

            node.statement_hash = statement_hash(node.statement)
        self.db.execute(
            """INSERT INTO nodes(id, name, rank, parent, depth, epoch, statement_status, proof_status,
                                 statement, statement_hash, closure_hash, preamble_hash, mockable, is_glue,
                                 owner, intent, budget, cost, attempts, file, body, evidence, ordering,
                                 created_at, updated_at)
               VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
            (
                node.id, node.name, node.rank, node.parent, node.depth, node.epoch,
                node.statement_status, node.proof_status, node.statement, node.statement_hash,
                node.closure_hash, node.preamble_hash, int(node.mockable), int(node.is_glue),
                node.owner, node.intent, node.budget.to_json(), json.dumps(node.cost),
                node.attempts, node.file, node.body, node.evidence, node.ordering,
                node.created_at, node.updated_at,
            ),
        )
        self.db.commit()
        self.emit("node.added", node.id, name=node.name, rank=node.rank, parent=node.parent)
        return node

    def get(self, node_id: str) -> Node | None:
        row = self.db.execute("SELECT * FROM nodes WHERE id=?", (node_id,)).fetchone()
        return _row_to_node(row) if row else None

    def by_name(self, name: str) -> Node | None:
        row = self.db.execute("SELECT * FROM nodes WHERE name=?", (name,)).fetchone()
        return _row_to_node(row) if row else None

    def nodes(self, **where: Any) -> list[Node]:
        clause = " AND ".join(f"{k}=?" for k in where)
        sql = "SELECT * FROM nodes" + (f" WHERE {clause}" if clause else "") + " ORDER BY ordering, created_at"
        return [_row_to_node(r) for r in self.db.execute(sql, tuple(where.values())).fetchall()]

    def update(self, node_id: str, **fields: Any) -> Node | None:
        if not fields:
            return self.get(node_id)
        if "body" in fields and fields["body"] is not None and not self._proof_write_allowed:
            raise RoleViolation(
                f"refusing to attach a proof to {node_id!r} outside record_proof(): "
                "only a prover attempt may put proof text into the graph"
            )
        if "budget" in fields and isinstance(fields["budget"], Budget):
            fields["budget"] = fields["budget"].to_json()
        if "cost" in fields and isinstance(fields["cost"], dict):
            fields["cost"] = json.dumps(fields["cost"])
        if "mockable" in fields:
            fields["mockable"] = int(bool(fields["mockable"]))
        fields["updated_at"] = time.time()
        sets = ", ".join(f"{k}=?" for k in fields)
        self.db.execute(f"UPDATE nodes SET {sets} WHERE id=?", (*fields.values(), node_id))
        self.db.commit()
        return self.get(node_id)

    def set_proof_status(
        self,
        node_id: str,
        status: str,
        *,
        evidence: str = "",
        body: str | None = None,
        role: str = "prover",
    ) -> None:
        assert status in ProofStatus, status
        fields: dict[str, Any] = {"proof_status": status}
        if evidence:
            fields["evidence"] = evidence
        if body is not None:
            if role not in PROOF_BEARING_ROLES:
                raise RoleViolation(
                    f"role {role!r} may not attach a proof to {node_id!r}; "
                    "decomposers state obligations, provers prove them"
                )
            self._proof_write_allowed = True
            try:
                fields["body"] = body
                self.update(node_id, **fields)
            finally:
                self._proof_write_allowed = False
            self.emit("node.proof_status", node_id, status=status, evidence=evidence[:400], role=role)
            return
        self.update(node_id, **fields)
        self.emit("node.proof_status", node_id, status=status, evidence=evidence[:400], role=role)

    def record_proof(self, node_id: str, body: str, *, role: str = "prover", status: str = "gated") -> None:
        """The only way a proof reaches the graph."""
        self.set_proof_status(node_id, status, body=body, role=role)

    def freeze(self, node_id: str, *, closure_hash: str = "", preamble_hash: str = "") -> Node | None:
        fields: dict[str, Any] = {"statement_status": "frozen"}
        if closure_hash:
            fields["closure_hash"] = closure_hash
        if preamble_hash:
            fields["preamble_hash"] = preamble_hash
        node = self.update(node_id, **fields)
        self.emit("node.frozen", node_id, epoch=node.epoch if node else 0)
        return node

    # -- edges -------------------------------------------------------------
    def add_edge(self, src: str, dst: str, *, kind: str = "uses", pinned_epoch: int | None = None) -> None:
        """``src``'s proof references ``dst``, pinned to ``dst``'s current epoch.

        The pin is what makes staleness pure graph arithmetic: a proof is always of a
        specific statement epoch, and integration requires every edge to be current.
        """
        if pinned_epoch is None:
            target = self.get(dst)
            pinned_epoch = target.epoch if target else 0
        self.db.execute(
            "INSERT INTO edges(src, dst, pinned_epoch, kind) VALUES(?,?,?,?) "
            "ON CONFLICT(src, dst, kind) DO UPDATE SET pinned_epoch=excluded.pinned_epoch",
            (src, dst, pinned_epoch, kind),
        )
        self.db.commit()

    def deps(self, node_id: str) -> list[tuple[str, int, str]]:
        rows = self.db.execute("SELECT dst, pinned_epoch, kind FROM edges WHERE src=?", (node_id,)).fetchall()
        return [(r["dst"], r["pinned_epoch"], r["kind"]) for r in rows]

    def dependents(self, node_id: str) -> list[str]:
        rows = self.db.execute("SELECT src FROM edges WHERE dst=?", (node_id,)).fetchall()
        return [r["src"] for r in rows]

    def stale_edges(self, node_id: str) -> list[tuple[str, int, int]]:
        """Edges whose pinned epoch is behind the dependency's current epoch."""
        out = []
        for dst, pinned, _kind in self.deps(node_id):
            target = self.get(dst)
            if target and target.epoch != pinned:
                out.append((dst, pinned, target.epoch))
        return out

    def transitive_dependents(self, node_id: str) -> list[str]:
        seen: set[str] = set()
        stack = [node_id]
        while stack:
            cur = stack.pop()
            for src in self.dependents(cur):
                if src not in seen:
                    seen.add(src)
                    stack.append(src)
        return sorted(seen)

    # -- scheduling --------------------------------------------------------
    def frontier(self) -> list[Node]:
        """Every dispatchable node, non-mockable ones first.

        The whole frontier goes out at once: the concurrency cap is whatever the rate
        window and the session pool allow, never a smaller number.  `non-mockable`
        nodes genuinely block their dependents, so they are scheduled first.
        """
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
    def start_attempt(self, node_id: str, *, runner: str, owner: str, role: str = "prover") -> int:
        """Record the start of one attempt.

        `owner` is who *stated* this obligation -- a human, or the decomposer that
        proposed it -- and is quite separate from which model tier is running the
        attempt, which `runner` and `role` carry. It was emitted under the name
        `tier`, so a prover attempt on a decomposer-proposed child read as
        `tier: decomposer` in the trace: exactly the model-attribution question the
        records exist to answer, answered wrongly. (The column keeps its old name so
        that graphs from earlier runs still open.)
        """
        node = self.get(node_id)
        cur = self.db.execute(
            "INSERT INTO attempts(node, epoch, runner, tier, role, started, status) "
            "VALUES(?,?,?,?,?,?,?)",
            (node_id, node.epoch if node else 0, runner, owner, role, time.time(), "claimed"),
        )
        self.db.execute("UPDATE nodes SET attempts = attempts + 1, updated_at=? WHERE id=?", (time.time(), node_id))
        self.db.commit()
        self.emit("attempt.started", node_id, runner=runner, owner=owner, role=role,
                  attempt=cur.lastrowid)
        return int(cur.lastrowid or 0)

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
        # The *resolved* model, not the runner's label.  "claude:default" names no
        # model, and a run whose most consequential decision cannot be attributed to
        # a model is a run you cannot draw a conclusion from.
        self.db.execute(
            "UPDATE attempts SET finished=?, status=?, evidence=?, body=?, gate=?, cost=?, "
            "requests=?, model=? WHERE id=?",
            (
                time.time(), status, evidence, body,
                json.dumps(gate or {}, default=str), json.dumps(cost or {}, default=str),
                json.dumps(requests or []), model, attempt_id,
            ),
        )
        self.db.commit()
        row = self.db.execute("SELECT node FROM attempts WHERE id=?", (attempt_id,)).fetchone()
        self.emit("attempt.finished", row["node"] if row else None, status=status, attempt=attempt_id)

    def attempts_for(self, node_id: str) -> list[dict[str, Any]]:
        rows = self.db.execute(
            "SELECT * FROM attempts WHERE node=? ORDER BY id", (node_id,)
        ).fetchall()
        return [dict(r) for r in rows]

    # -- lifecycle ---------------------------------------------------------
    def close(self) -> None:
        self.db.close()

    def __enter__(self) -> "Graph":
        return self

    def __exit__(self, *exc: object) -> None:
        self.close()
