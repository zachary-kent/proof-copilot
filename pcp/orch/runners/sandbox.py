"""Worker isolation, for benchmarks that must not be looked up.

PLAN.md 13 wants held-out lemmas from public developments (`iris-examples`,
`actris`, `reloc`).  Those solutions are on the internet, and — less obviously — they
are on *this machine*: an agent session's own transcript is a file under `$HOME`, and
if the operator ever pasted the reference proof into a session, a worker with `Bash`
can grep it out.  A solve rate measured without closing those doors measures nothing.

So this wraps a runner's command in `bwrap` with an **allowlist**, not a blocklist:

* no network at all (`--unshare-net`);
* `$HOME` replaced by a tmpfs, with only the provider's credential files bound back,
  so session transcripts, shell history and other checkouts are simply not there;
* the repo read-only, with the answer-key directory masked;
* exactly one writable directory: the node's own workdir.

What this does **not** do, and cannot: prevent a model from having memorised a public
proof. Anonymised identifiers make recall harder, not impossible. Treat results on a
public corpus as an upper bound and compare against a private one.
"""

from __future__ import annotations

import os
import shutil
import threading
import time
from dataclasses import dataclass, field, replace
from pathlib import Path

#: Files each provider needs to stay logged in.  Everything else under its config
#: directory -- transcripts, history, session state -- is deliberately absent.
CREDENTIAL_FILES: dict[str, tuple[str, ...]] = {
    "claude": (".claude/.credentials.json", ".claude/config.json", ".claude/settings.json", ".claude.json"),
    "codex": (".codex/auth.json", ".codex/config.toml"),
}

#: Hosts that carry *mechanisations* -- code forges and code search.  Blackholed in
#: the sandbox's `/etc/hosts`.
#:
#: This is affordable only because the worker does not need them: the Iris and stdpp
#: sources it is compiling against are bound into the sandbox, and `pcp docs` builds
#: a grep-able index of every declaration in them.  That is better documentation than
#: a web search, and it is the same version as the goal.
#:
#: Documentation *sites* stay reachable -- they carry papers and manuals, not proof
#: scripts (see :data:`ALLOWED_DOC_HOSTS`).
#:
#: Defence in depth only: this stops an agent that reaches for a URL, not one that
#: reaches for an IP. `network=False` is the only airtight mode.
SOLUTION_HOSTS: tuple[str, ...] = (
    "github.com", "www.github.com", "raw.githubusercontent.com", "gist.github.com",
    "codeload.github.com", "objects.githubusercontent.com", "api.github.com",
    "gitlab.com", "gitlab.mpi-sws.org", "gitlab.inria.fr", "bitbucket.org",
    "sourcegraph.com", "grep.app", "searchcode.com", "huggingface.co",
    "google.com", "www.google.com", "bing.com", "duckduckgo.com", "search.marginalia.nu",
)

#: Left reachable on purpose: manuals, tutorials and papers.  Blocking these would
#: make the benchmark measure "can it work without documentation", which is not the
#: question.  Listed for the record -- nothing is done to them.
ALLOWED_DOC_HOSTS: tuple[str, ...] = (
    "iris-project.org", "plv.mpi-sws.org", "rocq-prover.org", "coq.inria.fr",
    "coq.github.io", "stackoverflow.com", "arxiv.org",
)


def bwrap_binary() -> str | None:
    return os.environ.get("PCP_BWRAP") or shutil.which("bwrap")


def available() -> bool:
    return bwrap_binary() is not None


@dataclass
class Sandbox:
    """An allowlist sandbox for one worker attempt."""

    workdir: Path
    #: Read-only paths the worker legitimately needs (toolchain, the repo, python).
    ro_paths: list[Path] = field(default_factory=list)
    #: Paths to blank out *after* the read-only binds -- the answer key, the graph.
    masked: list[Path] = field(default_factory=list)
    #: Provider credential files, relative to the real home.
    credentials: list[str] = field(default_factory=list)
    #: Binaries the worker must be able to execute.  Their real paths' directories
    #: are bound read-only -- `claude` lives under `$HOME`, which is otherwise gone.
    binaries: list[str] = field(default_factory=list)
    network: bool = False
    #: Hosts blackholed in the sandbox's `/etc/hosts` when the network *is* up.
    deny_hosts: tuple[str, ...] = ()
    #: Documentation bound back *after* masking -- the local Iris index.
    docs_paths: list[Path] = field(default_factory=list)
    #: Paths bound back read-only after masking.  Used to carve the one corpus a run
    #: is allowed to see out of a `masked` corpus tree.
    unmasked: list[Path] = field(default_factory=list)
    home: Path = field(default_factory=lambda: Path.home())
    env_passthrough: tuple[str, ...] = (
        "PATH", "LANG", "LC_ALL", "TERM", "ROCQPATH", "COQPATH", "OCAMLPATH",
        "PCP_COQC", "PCP_PET", "PCP_PET_SERVER",
    )

    def wrap(self, argv: list[str]) -> list[str]:
        bwrap = bwrap_binary()
        if bwrap is None:
            raise RuntimeError("bwrap is not installed; sandboxed runs need bubblewrap")
        home = self.home.resolve()
        cmd: list[str] = [bwrap, "--die-with-parent", "--new-session"]
        if not self.network:
            cmd.append("--unshare-net")

        # System paths: read-only, and only the ones a build needs.
        for path in ("/usr", "/bin", "/sbin", "/lib", "/lib64", "/etc", "/opt"):
            if Path(path).exists():
                cmd += ["--ro-bind", path, path]
        hosts_file = self._hosts_file()
        if hosts_file is not None:
            cmd += ["--ro-bind", str(hosts_file), "/etc/hosts"]
        cmd += ["--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp", "--tmpfs", "/run"]
        if self.network:
            # `/etc/resolv.conf` is usually a symlink into `/run`, which the tmpfs
            # above has just replaced -- so DNS dies silently and every fetch looks
            # like a network failure rather than a configuration one.  Bind the real
            # file back over the link.
            resolv = Path("/etc/resolv.conf")
            if resolv.exists():
                real = resolv.resolve()
                # Bind to the *resolved* path: `/etc` is read-only here, and when
                # resolv.conf is a symlink into `/run` the link target must be the
                # thing that exists, not the link itself.
                target = str(real) if real != resolv else "/etc/resolv.conf"
                cmd += ["--ro-bind", str(real), target]

        # The home directory is replaced wholesale, then rebuilt from an allowlist.
        # This is the step that removes session transcripts and stray checkouts.
        cmd += ["--tmpfs", str(home)]
        for path in self.ro_paths:
            resolved = Path(path).resolve()
            if resolved.exists():
                cmd += ["--ro-bind", str(resolved), str(resolved)]
        # Masking comes after the binds, so a read-only repo can still have its
        # answer-key directory blanked out.
        for path in self.masked:
            cmd += ["--tmpfs", str(Path(path).resolve())]
        # Credentials are staged into a directory and the *directory* is bound, never
        # the individual files.  `--ro-bind <file>` pins an inode, and an OAuth refresh
        # replaces the credentials file by atomic rename -- so every worker spawned
        # before a refresh kept reading the old inode and got
        # `401 OAuth access token has been revoked` the moment the host rotated.  That
        # killed the 2026-09-01 design ladder 20 minutes in, and had eaten rungs
        # before.  Binding `~/.claude` itself is not the fix: it holds session
        # transcripts, which is exactly what this sandbox exists to remove.  So only
        # the allowlisted files are copied into the stage, and a rename inside the
        # bound directory *is* visible to a running worker.
        for host_dir, stage_dir in _stage_credentials(self.credentials, home):
            cmd += ["--ro-bind", str(stage_dir), str(host_dir)]
        for rel in self.credentials:
            src = home / rel
            if src.exists() and src.parent == home:
                # A file sitting directly in `$HOME` has no directory to stage into --
                # `$HOME` is the tmpfs this sandbox is built on.  These are config, not
                # the rotating OAuth token, so a pinned inode is harmless here.
                cmd += ["--ro-bind", str(src), str(src)]
        for binary in self.binaries:
            for path in _binary_paths(binary):
                cmd += ["--ro-bind", str(path), str(path)]

        for path in [*self.docs_paths, *self.unmasked]:
            resolved = Path(path).resolve()
            if resolved.exists():
                cmd += ["--ro-bind", str(resolved), str(resolved)]

        # Exactly one writable place.
        work = self.workdir.resolve()
        cmd += ["--bind", str(work), str(work), "--chdir", str(work)]

        cmd += ["--setenv", "HOME", str(home)]
        cmd += ["--setenv", "PCP_SANDBOX", "1"]
        for name in self.env_passthrough:
            value = os.environ.get(name)
            if value:
                cmd += ["--setenv", name, value]
        cmd.append("--")
        cmd += argv
        return cmd

    def _hosts_file(self) -> Path | None:
        """A `/etc/hosts` that blackholes the solution hosts.

        Only meaningful when the network is up; with ``network=False`` there is
        nothing to resolve.  The file is content-addressed and reused across
        concurrent sandboxes: a fresh temp file per attempt races with `/tmp`
        cleanup and produces a `Can't find source path` failure that looks like a
        worker error and is not.
        """
        if not self.network or not self.deny_hosts:
            return None
        return _hosts_file_for(self.deny_hosts)

    @classmethod
    def for_benchmark(
        cls,
        workdir: Path,
        *,
        repo: Path,
        toolchain: Path | None = None,
        reference: Path | None = None,
        provider: str = "claude",
        network: bool = True,
        binaries: list[str] | None = None,
        docs: Path | None = None,
        corpus: Path | None = None,
        library: list[Path] | None = None,
    ) -> "Sandbox":
        """The configuration a held-out-lemma benchmark should use.

        ``network=True`` by default because a subscription-backed CLI worker has to
        reach its provider to think at all.  The lookup control in that mode is the
        *tool allowlist* (the worker is given no web tool and a Bash restricted to
        the checker) plus the host blackhole; the masked home removes the local
        copies.  ``network=False`` is airtight but only usable with a runner that
        executes the model outside the sandbox.
        """
        repo = Path(repo).resolve()
        ro = [repo]
        if toolchain is None:
            toolchain = Path.home() / ".opam"
        ro.append(Path(toolchain))
        masked = [repo / ".pcp"]
        if reference is not None:
            masked.append(Path(reference).resolve())
        # The repo is bound read-only in full, and the repo is not innocent.  A
        # worker needs exactly four things: the `pcp` package (to run `pcp check`),
        # the toolchain, its own corpus, and the Iris index.  Everything else in the
        # tree is a channel, and three of them were live:
        #
        # * `eval/corpus/` holds every *other* rung.  For a design rung that is the
        #   answer -- the sibling rung is the same development with the design
        #   **given**: the real invariant, the ghost state, the helper lemmas with
        #   their proofs, and a DESIGN.md carrying the author's strategy in prose.
        #   Anonymisation renames it; it does not withhold it.
        # * `docs/` explains the benchmarks, which means it quotes them -- including
        #   the reference shape of a predicate a rung asks a worker to invent.
        # * `.git` can hold any earlier state of any of the above, pre-scrub.
        #
        # `tests/` goes for the same reason as `docs/`: fixtures are made of real
        # examples.  The one rung under test is bound back afterwards.
        unmasked: list[Path] = []
        for extra in (repo / ".git", repo / "eval", repo / "docs", repo / "tests"):
            if extra.exists():
                masked.append(extra)
        if corpus is not None:
            unmasked.append(Path(corpus).resolve())
        # A ladder rung may be given what *this system* produced on the rungs below
        # it, and published reading -- the way a person carries their own last proof
        # and a paper into the next problem.  Deliberately narrow: these are curated
        # directories, bound after the masks, and they must never contain a corpus
        # reference proof.  `eval/corpus` stays masked either way, so the only route
        # in is the one the operator explicitly opened.
        for extra in library or []:
            unmasked.append(Path(extra).resolve())
        # The docs index lives under `.pcp`, which was just masked; bind it back so
        # the worker keeps its documentation but not the answer key.
        docs = docs if docs is not None else repo / ".pcp" / "docs"
        return cls(
            workdir=workdir,
            ro_paths=ro,
            masked=masked,
            credentials=list(CREDENTIAL_FILES.get(provider, ())),
            binaries=binaries if binaries is not None else [provider, "python3", "pcp"],
            network=network,
            deny_hosts=SOLUTION_HOSTS,
            docs_paths=[Path(docs)] if docs else [],
            unmasked=unmasked,
        )


_HOSTS_CACHE: dict[str, Path] = {}


def _hosts_file_for(deny: tuple[str, ...]) -> Path:
    import hashlib
    import tempfile

    key = hashlib.blake2b("\n".join(deny).encode(), digest_size=8).hexdigest()
    cached = _HOSTS_CACHE.get(key)
    if cached is not None and cached.exists():
        return cached
    base = Path("/etc/hosts").read_text(encoding="utf-8") if Path("/etc/hosts").exists() else ""
    lines = [base, "", "# pcp benchmark isolation: mechanisation hosts are blackholed"]
    for host in deny:
        lines.append(f"127.0.0.1 {host}")
        lines.append(f"::1 {host}")
    root = Path(tempfile.gettempdir()) / "pcp-sandbox"
    root.mkdir(parents=True, exist_ok=True)
    path = root / f"hosts-{key}"
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    _HOSTS_CACHE[key] = path
    return path


#: Host credential file -> its staged copy, for the background refresher.
_CRED_STAGED: dict[Path, Path] = {}
_CRED_LOCK = threading.Lock()
_CRED_REFRESHER: threading.Thread | None = None
#: How often the stage is re-synced from the host.  A worker can outlive several
#: token refreshes -- a design round is budgeted at 5400 s -- and it reads the stage
#: live, so the stage has to keep up on its own rather than only at spawn time.
CRED_REFRESH_SECONDS = 60.0


def _copy_credential(src: Path, dst: Path) -> None:
    """Refresh one staged file, atomically and with the source's permissions.

    Written to a temporary name in the *same* directory and renamed, so a worker
    reading the stage never sees a half-written token.
    """
    dst.parent.mkdir(parents=True, exist_ok=True)
    tmp = dst.with_name(dst.name + ".pcp-new")
    shutil.copyfile(src, tmp)
    os.chmod(tmp, os.stat(src).st_mode & 0o777)
    os.replace(tmp, dst)


def sync_credentials() -> int:
    """Re-copy any staged credential whose source has changed.  Returns how many.

    Compares *content*, not `(mtime, size)`.  A token file is a few hundred bytes, so
    hashing it is free, and the cheap comparison has a real hole: a rotation that
    lands in the same filesystem timestamp tick and keeps the same length would be
    skipped, leaving the worker on a revoked token -- the exact failure this staging
    exists to prevent, made rarer and therefore harder to diagnose.
    """
    changed = 0
    with _CRED_LOCK:
        items = list(_CRED_STAGED.items())
    for src, dst in items:
        try:
            if not src.exists():
                continue
            current = src.read_bytes()
            if dst.exists() and dst.read_bytes() == current:
                continue
            _copy_credential(src, dst)
            changed += 1
        except OSError:
            # A credential that cannot be staged must not take the run down; the
            # worker will fail its own auth check and be classified as such.
            continue
    return changed


def _start_credential_refresher() -> None:
    global _CRED_REFRESHER
    if _CRED_REFRESHER is not None:
        return

    def _loop() -> None:
        while True:
            time.sleep(CRED_REFRESH_SECONDS)
            sync_credentials()

    _CRED_REFRESHER = threading.Thread(target=_loop, name="pcp-credential-refresh", daemon=True)
    _CRED_REFRESHER.start()


def _stage_credentials(credentials: list[str], home: Path) -> list[tuple[Path, Path]]:
    """Copy allowlisted credential files into per-directory stages.

    Returns ``(host_dir, stage_dir)`` pairs to bind.  Only files named in
    ``credentials`` are ever copied, so the stage is an allowlist by construction --
    the same guarantee the per-file binds gave, minus the pinned inode.
    """
    import hashlib
    import tempfile

    by_parent: dict[Path, list[Path]] = {}
    for rel in credentials:
        src = home / rel
        if src.exists() and src.parent != home:
            by_parent.setdefault(src.parent, []).append(src)
    if not by_parent:
        return []

    root = Path(tempfile.gettempdir()) / "pcp-sandbox"
    root.mkdir(parents=True, exist_ok=True)
    out: list[tuple[Path, Path]] = []
    for host_dir, files in sorted(by_parent.items()):
        key = hashlib.blake2b(str(host_dir).encode(), digest_size=8).hexdigest()
        stage = root / f"creds-{os.getuid()}-{key}"
        stage.mkdir(parents=True, exist_ok=True)
        os.chmod(stage, 0o700)
        for src in files:
            dst = stage / src.name
            with _CRED_LOCK:
                _CRED_STAGED[src] = dst
        out.append((host_dir, stage))
    sync_credentials()
    _start_credential_refresher()
    return out


def _binary_paths(name: str) -> list[Path]:
    """The directories needed to execute ``name``: its symlink and its real target."""
    found = shutil.which(name)
    if not found:
        return []
    out: list[Path] = []
    link = Path(found)
    real = link.resolve()
    for candidate in (link.parent, real.parent):
        if candidate.exists() and candidate not in out:
            out.append(candidate)
    return out


@dataclass
class SandboxedRunner:
    """Wraps another runner so its subprocess runs inside a :class:`Sandbox`.

    Delegates everything else -- the runner keeps its own prompt handling, deadline
    ladder and answer parsing.  Only the argv changes.
    """

    inner: object
    sandbox_factory: object  # Callable[[Path], Sandbox]
    name: str = ""

    def __post_init__(self) -> None:
        if not self.name:
            self.name = f"sandboxed:{getattr(self.inner, 'name', 'runner')}"

    def available(self) -> bool:
        return available() and bool(self.inner.available())  # type: ignore[attr-defined]

    async def run_node(self, node):  # type: ignore[no-untyped-def]
        from pcp.orch.runners.base import NodeResult

        if not available():
            return NodeResult(
                status="error",
                evidence="bwrap is not installed; refusing to run a benchmark worker unsandboxed",
            )
        # Never mutate the wrapped runner: the whole frontier dispatches at once, so
        # a shared `argv` that is swapped in and restored races -- and the attempt
        # that loses the race runs with another node's sandbox, or none at all.
        import copy

        inner = copy.copy(self.inner)
        sandbox = self.sandbox_factory(node.workdir)  # type: ignore[operator]
        # The development moves when a design is adopted: it is rewritten under the
        # work root, which is masked so that one worker cannot read another's
        # scratch.  The file the worker is proving *against* has to come back, or
        # `pcp check` cannot open it -- `Development(meta["file"])` reads eagerly, so
        # the worker's whole check loop dies on the first call with a path that only
        # exists outside its sandbox.  Harmless to bind: it is the design under test,
        # which the worker is given anyway.
        source_dir = Path(node.file).resolve().parent if getattr(node, "file", "") else None
        if source_dir is not None and source_dir not in sandbox.unmasked:
            sandbox = replace(sandbox, unmasked=[*sandbox.unmasked, source_dir])
        inner.argv = sandbox.wrap(list(self.inner.argv))  # type: ignore[attr-defined]
        return await inner.run_node(node)  # type: ignore[attr-defined]
