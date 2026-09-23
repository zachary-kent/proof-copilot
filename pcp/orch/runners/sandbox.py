"""Worker isolation, for benchmarks that must not be looked up (PLAN.md 6, 13).

Held-out lemmas from public developments have their solutions on the internet, and --
less obviously -- on *this machine*: an agent session's own transcript is a file under
``$HOME``, and if the operator ever pasted the reference proof into a session, a worker
with ``Bash`` can grep it out.  So this wraps a runner's command in ``bwrap`` with an
**allowlist**, not a blocklist:

* ``$HOME`` replaced by a tmpfs, with only the provider's credential files bound back;
* the project read-only with the answer-key subtrees masked, and pcp's own install
  (interpreter prefix, package, ``pcp`` entry point) read-only so ``pcp check`` runs
  whether pcp is a checkout's venv or a ``uv tool`` install under ``$HOME``;
* exactly one writable directory: the attempt's own workdir;
* an explicit environment allowlist (``SANDBOX_PASSTHROUGH`` + ``HOME`` +
  ``PCP_SANDBOX``): nothing else may enter a worker's environment, API keys included
  (PLAN.md 11, "nothing secret may ever enter them").  Enforced
  twice: :meth:`Sandbox.environment` is what the ``bwrap`` process itself is started
  with (so nothing else exists to inherit, on any bubblewrap), and ``--clearenv`` +
  ``--setenv`` are emitted as well where the binary supports them (bubblewrap >= 0.5);
* ``--unshare-pid`` so the worker's whole tree dies with it -- ``coqc``, ``pcp mcp``,
  petanque -- instead of surviving the deadline kill.

:meth:`Sandbox.wrap` is a pure function of its arguments: it never mutates the wrapped
runner's argv (a shared argv swapped in and restored raced across the frontier and ran
one node in another node's sandbox), and the same inputs give the same command line.
Its only side effects are idempotent host-side staging: the content-addressed hosts
file and the credential stage, both per uid and written atomically.

What this does **not** do, and cannot: prevent a model from having memorised a public
proof.  Treat results on a public corpus as an upper bound.
"""

from __future__ import annotations

import copy
import os
import shutil
import sys
import tempfile
import threading
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from pcp.config.env import SANDBOX, SANDBOX_PASSTHROUGH, bwrap_binary, opam_root, with_runner_defaults
from pcp.errors import ToolchainError
from pcp.orch.protocol import NodePayload, NodeResult
from pcp.util.hashing import content_hash, short_hash
from pcp.util.io import atomic_write_text, read_text
from pcp.util.paths import home as user_home
from pcp.util.paths import tmpdir
from pcp.util.proc import run

__all__ = [
    "CHECKOUT_MASKS",
    "CREDENTIAL_FILES",
    "SOLUTION_HOSTS",
    "Sandbox",
    "SandboxedRunner",
    "available",
    "bwrap_binary",
    "install_paths",
    "stage_credentials",
    "sync_credentials",
]

#: Files each provider needs to stay logged in.  Everything else under its config
#: directory -- transcripts, history, session state -- is deliberately absent.
CREDENTIAL_FILES: dict[str, tuple[str, ...]] = {
    "anthropic": (".claude/.credentials.json", ".claude/config.json", ".claude/settings.json", ".claude.json"),
    "codex": (".codex/auth.json", ".codex/config.toml"),
}
PROVIDER_BINARIES: dict[str, str] = {"anthropic": "claude", "codex": "codex"}
_PROVIDER_ALIASES = {"claude": "anthropic", "claude-code": "anthropic"}

#: Hosts that carry *mechanisations* -- code forges and code search -- blackholed in
#: the sandbox's ``/etc/hosts``.  Affordable because the worker does not need them:
#: the Iris and stdpp sources are bound in and ``pcp docs`` indexes every declaration.
#: Documentation sites stay reachable.  Defence in depth only: it stops an agent that
#: reaches for a URL, not one that reaches for an IP; ``network=False`` is airtight.
SOLUTION_HOSTS: tuple[str, ...] = (
    "github.com", "www.github.com", "raw.githubusercontent.com", "gist.github.com",
    "codeload.github.com", "objects.githubusercontent.com", "api.github.com",
    "gitlab.com", "gitlab.mpi-sws.org", "gitlab.inria.fr", "bitbucket.org",
    "sourcegraph.com", "grep.app", "searchcode.com", "huggingface.co",
    "google.com", "www.google.com", "bing.com", "duckduckgo.com", "search.marginalia.nu",
)

SYSTEM_PATHS: tuple[str, ...] = ("/usr", "/bin", "/sbin", "/lib", "/lib64", "/etc", "/opt")

#: Subtrees of a proof-copilot *checkout* that quote the benchmarks (for_benchmark's
#: docstring).  A user's own project gets only ``.pcp`` masked: its docs/ and tests/
#: are its own, not an answer key.
CHECKOUT_MASKS: tuple[str, ...] = (".git", "eval", "docs", "tests")

#: How often the credential stage is re-synced.  A worker can outlive several token
#: refreshes (a design round is budgeted at 5400 s) and reads the stage live.
CRED_REFRESH_SECONDS = 60.0


def available() -> bool:
    return bwrap_binary() is not None


_CLEARENV_SUPPORT: dict[str, bool] = {}
_CLEARENV_LOCK = threading.Lock()


def supports_clearenv(bwrap: str) -> bool:
    """Whether this bubblewrap knows ``--clearenv`` (0.5+); probed once per binary."""
    with _CLEARENV_LOCK:
        if bwrap in _CLEARENV_SUPPORT:
            return _CLEARENV_SUPPORT[bwrap]
    probe = run([bwrap, "--help"], timeout=10)
    supported = not probe.spawn_error and "--clearenv" in probe.output
    with _CLEARENV_LOCK:
        _CLEARENV_SUPPORT[bwrap] = supported
    return supported


def provider_key(provider: str) -> str:
    return _PROVIDER_ALIASES.get(provider, provider)


def stage_root() -> Path:
    """Per-uid, 0700: two users on one box never share a stage, and the root is not
    created with the umask."""
    root = tmpdir() / f"pcp-sandbox-{os.getuid()}"
    root.mkdir(parents=True, exist_ok=True)
    os.chmod(root, 0o700)
    return root


@dataclass(frozen=True)
class Sandbox:
    """An allowlist sandbox policy, applied per attempt by :meth:`wrap`."""

    #: Read-only paths the worker legitimately needs (the repo, the toolchain).
    ro_paths: tuple[Path, ...] = ()
    #: Paths blanked out *after* the read-only binds -- the answer key, the graph.
    masked: tuple[Path, ...] = ()
    #: Provider credential files, relative to the real home.
    credentials: tuple[str, ...] = ()
    #: Binaries the worker must execute; their directories are bound read-only.
    binaries: tuple[str, ...] = ()
    network: bool = True
    deny_hosts: tuple[str, ...] = ()
    #: Bound back after masking: the local Iris index.
    docs_paths: tuple[Path, ...] = ()
    #: Bound back after masking: the corpus under test, curated libraries.
    unmasked: tuple[Path, ...] = ()
    home: Path = field(default_factory=user_home)
    env_passthrough: tuple[str, ...] = SANDBOX_PASSTHROUGH
    #: Where hosts files and credential stages live; default ``$TMPDIR/pcp-sandbox-<uid>``.
    root: Path | None = None
    #: Off in tests: the refresher is a daemon thread that outlives the sandbox object.
    refresh_credentials: bool = True
    #: Emit ``--clearenv``: ``None`` probes the binary, ``True``/``False`` force it.
    clearenv: bool | None = None

    def environment(self, env: Mapping[str, str] | None = None) -> dict[str, str]:
        """The allowlisted environment the sandboxed command runs with -- and the
        environment the ``bwrap`` process itself must be started with."""
        environ = with_runner_defaults(env)
        out = {"HOME": str(self.home.resolve()), SANDBOX: "1"}
        for name in self.env_passthrough:
            value = environ.get(name)
            if value:
                out[name] = value
        return out

    @classmethod
    def for_benchmark(
        cls,
        repo: Path,
        *,
        reference: Path | None = None,
        corpus_dir: Path | None = None,
        library: Sequence[Path] = (),
        network: bool = True,
        provider: str = "anthropic",
        toolchain: Path | None = None,
        docs: Path | None = None,
        binaries: Sequence[str] | None = None,
        home: Path | None = None,
        root: Path | None = None,
        masks: Sequence[str | Path] = CHECKOUT_MASKS,
        install: Sequence[Path] | None = None,
    ) -> Sandbox:
        """The configuration a held-out-lemma benchmark uses (contract 3.4).

        ``repo`` is the project root, bound read-only in full.  In a proof-copilot
        checkout it is not innocent: ``eval/`` holds every *other* rung (for a design
        rung, the same development with the design given), ``docs/`` quotes the
        benchmarks, ``tests/`` fixtures are real examples, ``.git`` holds pre-scrub
        history -- those are ``masks`` (default :data:`CHECKOUT_MASKS`; pass ``()`` for
        a user's project).  ``.pcp`` holds the answer key and every earlier run and is
        always masked; the corpus under test, the docs index and any curated library
        are carved back out afterwards.  ``install`` (default :func:`install_paths`)
        is pcp's own installation, bound read-only so ``pcp check`` exists inside.
        """
        repo = Path(repo).resolve()
        real_home = Path(home) if home is not None else user_home()
        ro = [repo, Path(toolchain) if toolchain is not None else opam_root()]
        ro += [Path(p) for p in (install if install is not None else install_paths())]
        masked = list(dict.fromkeys([repo / ".pcp", *(repo / sub for sub in masks)]))
        if reference is not None:
            masked.append(Path(reference).resolve())
        unmasked = [Path(corpus_dir).resolve()] if corpus_dir is not None else []
        unmasked += [Path(p).resolve() for p in library]
        key = provider_key(provider)
        return cls(
            ro_paths=tuple(ro),
            masked=tuple(masked),
            credentials=CREDENTIAL_FILES.get(key, ()),
            binaries=tuple(binaries) if binaries is not None else (PROVIDER_BINARIES.get(key, key), "python3", "pcp"),
            network=network,
            deny_hosts=SOLUTION_HOSTS,
            docs_paths=(Path(docs) if docs is not None else repo / ".pcp" / "docs",),
            unmasked=tuple(unmasked),
            home=real_home,
            root=root,
            refresh_credentials=True,
        )

    # ---------------------------------------------------------------- wrap

    def wrap(
        self,
        argv: Sequence[str],
        *,
        workdir: Path,
        node_file_dir: Path | None = None,
        env: Mapping[str, str] | None = None,
    ) -> list[str]:
        """The bwrap command line for one attempt (mount order: contract 3.4).

        ``node_file_dir`` is the directory of the development the worker proves
        against: after a design is adopted it lives under the masked work root, and
        ``pcp check`` opens it eagerly, so only that directory is bound back.

        Mount order is *most specific wins*: every mount is emitted shallowest target
        first (:class:`_Mounts`), so a bind can never undo a mask beneath it -- a
        carve-back of the project root (``pcp prove F.v`` with ``F.v`` at the root)
        leaves ``.pcp`` and ``--reference`` hidden -- and a path is visible only if
        the deepest rule on its ancestry is a bind.  At equal depth a mask beats a
        bind of the same path.
        """
        bwrap = bwrap_binary()
        if bwrap is None:
            raise ToolchainError("bwrap is not installed; sandboxed runs need bubblewrap")
        home = self.home.resolve()
        root = self.root if self.root is not None else stage_root()
        cmd: list[str] = [bwrap, "--die-with-parent", "--new-session", "--unshare-pid"]
        if not self.network:
            cmd.append("--unshare-net")
        mounts = _Mounts()
        for system in SYSTEM_PATHS:
            if Path(system).exists():
                mounts.bind(Path(system))
        if self.network and self.deny_hosts:
            mounts.add(Path("/etc/hosts"), _BIND, ["--ro-bind", str(hosts_file(self.deny_hosts, root)), "/etc/hosts"])
        mounts.add(Path("/proc"), _BIND, ["--proc", "/proc"])
        mounts.add(Path("/dev"), _BIND, ["--dev", "/dev"])
        mounts.mask(Path("/tmp"))
        mounts.mask(Path("/run"))
        if self.network:
            # ``/etc/resolv.conf`` is usually a symlink into ``/run``, which the tmpfs
            # just replaced; bind the *resolved* file back or DNS dies silently.
            resolv = Path("/etc/resolv.conf")
            if resolv.exists():
                real = resolv.resolve()
                target = real if real != resolv else resolv
                mounts.add(target, _BIND, ["--ro-bind", str(real), str(target)])
        mounts.mask(home)
        for path in self.ro_paths:
            resolved = Path(path).resolve()
            if resolved.exists():
                mounts.bind(resolved)
        # A mask that does not exist is skipped: nothing there can leak, and bwrap
        # cannot create a mount point inside a read-only bind.
        for path in self.masked:
            resolved = Path(path).resolve()
            if resolved.exists():
                mounts.mask(resolved)
        # Credentials: a *directory* stage is bound, never the files.  ``--ro-bind
        # <file>`` pins an inode, and an OAuth refresh replaces the file by rename --
        # every worker spawned before the rotation kept the revoked token.
        for host_dir, stage_dir in stage_credentials(self.credentials, home, root=root, refresh=self.refresh_credentials):
            mounts.add(host_dir, _BIND, ["--ro-bind", str(stage_dir), str(host_dir)])
        for rel in self.credentials:
            src = home / rel
            if src.exists() and src.parent == home:
                # Directly in ``$HOME`` (the tmpfs): config, not the rotating token.
                mounts.bind(src)
        for binary in self.binaries:
            for path in _binary_dirs(binary):
                mounts.bind(path)
        extra = [*self.docs_paths, *self.unmasked]
        if node_file_dir is not None:
            extra.append(Path(node_file_dir))
        for path in extra:
            resolved = Path(path).resolve()
            if resolved.exists():
                mounts.add(resolved, _CARVE, ["--ro-bind", str(resolved), str(resolved)])
        work = Path(workdir).resolve()
        mounts.add(work, _CARVE, ["--bind", str(work), str(work)])
        cmd += mounts.ordered()
        cmd += ["--chdir", str(work)]
        # The allowlist: ``--clearenv`` first (where known), then only what is named.
        clearenv = self.clearenv if self.clearenv is not None else supports_clearenv(bwrap)
        if clearenv:
            cmd.append("--clearenv")
        for name, value in self.environment(env).items():
            cmd += ["--setenv", name, value]
        cmd.append("--")
        cmd += [str(a) for a in argv]
        return cmd


# ---------------------------------------------------------------- mount ordering

#: Ranks among mounts of the *same* target: a mask is applied last, so it wins.
_BIND, _CARVE, _MASK = 0, 1, 2


class _Mounts:
    """bwrap mounts, emitted so the most specific rule on every path wins.

    bwrap applies mounts in argv order and a later mount on an ancestor covers
    everything beneath it, so a carve-back emitted after a mask it contains undid the
    mask (the project root bound back over its own ``.pcp``).  Sorting by target depth
    (stable, then by rank) makes the order irrelevant to the caller: an ancestor is
    always mounted before its descendants, whatever kind either is.
    """

    def __init__(self) -> None:
        self._mounts: list[tuple[int, int, int, list[str]]] = []

    def add(self, target: Path, rank: int, args: list[str]) -> None:
        self._mounts.append((len(Path(target).parts), rank, len(self._mounts), args))

    def bind(self, path: Path) -> None:
        self.add(path, _BIND, ["--ro-bind", str(path), str(path)])

    def mask(self, path: Path) -> None:
        # A tmpfs cannot be mounted on a file; an empty file blanks it instead.
        args = ["--tmpfs", str(path)] if path.is_dir() or not path.exists() else ["--ro-bind", "/dev/null", str(path)]
        self.add(path, _MASK, args)

    def ordered(self) -> list[str]:
        return [a for *_key, args in sorted(self._mounts, key=lambda m: m[:3]) for a in args]


# ---------------------------------------------------------------- host-side staging


def hosts_file(deny: Sequence[str], root: Path) -> Path:
    """A ``/etc/hosts`` that blackholes ``deny``, content-addressed and shared.

    A fresh temp file per attempt raced with ``/tmp`` cleanup and produced bwrap's
    "Can't find source path", which looked like a worker error.  Written atomically,
    so two orchestrators starting together cannot bind a half-written file.
    """
    base = read_text("/etc/hosts") if Path("/etc/hosts").exists() else ""
    lines = [base.rstrip("\n"), "", "# pcp benchmark isolation: mechanisation hosts are blackholed"]
    for host in deny:
        lines.append(f"127.0.0.1 {host}")
        lines.append(f"::1 {host}")
    content = "\n".join(lines) + "\n"
    path = Path(root) / f"hosts-{content_hash(content, prefix='', size=8)}"
    if not path.exists() or read_text(path) != content:
        atomic_write_text(path, content)
    return path


class _CredentialStage:
    """Staged credential copies plus the refresher that keeps them current.

    Compares *content*, not ``(mtime, size)``: a token file is a few hundred bytes and
    a rotation landing in the same timestamp tick with the same length would be
    missed -- the exact failure staging exists to prevent, made rarer.
    """

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._staged: dict[Path, Path] = {}
        self._thread: threading.Thread | None = None
        self._stop = threading.Event()

    def stage(self, credentials: Sequence[str], home: Path, *, root: Path, refresh: bool) -> list[tuple[Path, Path]]:
        by_parent: dict[Path, list[Path]] = {}
        for rel in credentials:
            src = home / rel
            if src.exists() and src.parent != home:
                by_parent.setdefault(src.parent, []).append(src)
        if not by_parent:
            return []
        out: list[tuple[Path, Path]] = []
        for host_dir, files in sorted(by_parent.items()):
            stage = Path(root) / f"creds-{short_hash(str(host_dir))}"
            stage.mkdir(parents=True, exist_ok=True)
            os.chmod(stage, 0o700)
            with self._lock:
                for src in files:
                    self._staged[src] = stage / src.name
            out.append((host_dir, stage))
        self.sync()
        if refresh:
            self.start()
        return out

    def sync(self) -> int:
        with self._lock:
            items = list(self._staged.items())
        changed = 0
        for src, dst in items:
            try:
                if not src.exists():
                    continue
                current = src.read_bytes()
                if dst.exists() and dst.read_bytes() == current:
                    continue
                _copy_atomically(src, dst, current)
                changed += 1
            except OSError:
                # A credential that cannot be staged must not take the run down; the
                # worker fails its own auth check and is classified as such.
                continue
        return changed

    def start(self) -> None:
        with self._lock:
            if self._thread is not None and self._thread.is_alive():
                return
            self._stop.clear()
            self._thread = threading.Thread(target=self._loop, name="pcp-credential-refresh", daemon=True)
            self._thread.start()

    def stop(self) -> None:
        self._stop.set()

    def _loop(self) -> None:
        while not self._stop.wait(CRED_REFRESH_SECONDS):
            self.sync()


_STAGE = _CredentialStage()


def stage_credentials(credentials: Sequence[str], home: Path, *, root: Path | None = None, refresh: bool = True) -> list[tuple[Path, Path]]:
    """Copy allowlisted credential files into per-directory stages; return the
    ``(host_dir, stage_dir)`` pairs to bind.  Only named files are ever copied, so
    the stage is an allowlist by construction."""
    return _STAGE.stage(credentials, Path(home), root=root if root is not None else stage_root(), refresh=refresh)


def sync_credentials() -> int:
    """Re-copy any staged credential whose source changed; returns how many."""
    return _STAGE.sync()


def _copy_atomically(src: Path, dst: Path, data: bytes) -> None:
    """A unique temp name in the same directory, then rename: two processes syncing
    the same stage cannot truncate each other's copy mid-write."""
    dst.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(prefix=f".{dst.name}.", dir=str(dst.parent))
    try:
        with os.fdopen(fd, "wb") as fh:
            fh.write(data)
        os.chmod(tmp, os.stat(src).st_mode & 0o777)
        os.replace(tmp, dst)
    except BaseException:
        with _suppress_oserror():
            os.unlink(tmp)
        raise


class _suppress_oserror:
    def __enter__(self) -> None:
        return None

    def __exit__(self, exc_type: Any, exc: Any, tb: Any) -> bool:
        return exc_type is not None and issubclass(exc_type, OSError)


def install_paths() -> list[Path]:
    """What running pcp needs from the host, besides the system and the toolchain:
    the interpreter's prefix and base prefix (a ``uv tool`` venv under
    ``~/.local/share/uv/tools`` and its managed Python under ``~/.local/share/uv/python``
    -- both inside the ``$HOME`` the sandbox replaces) and the package directory itself
    (an editable install's source).  The ``pcp`` entry point's directories are bound
    through ``binaries``."""
    import pcp

    home = user_home().resolve()
    out: list[Path] = []
    for raw in (sys.prefix, sys.base_prefix, Path(pcp.__file__).parent):
        path = Path(raw).resolve()
        # Never ``$HOME`` or an ancestor of it: that bind would undo the home tmpfs.
        if path.exists() and path not in out and path != home and path not in home.parents:
            out.append(path)
    return out


def _binary_dirs(name: str) -> list[Path]:
    """The directories needed to execute ``name``: its symlink's and its target's."""
    found = shutil.which(name)
    if not found:
        return []
    link = Path(found)
    out: list[Path] = []
    for candidate in (link.parent, link.resolve().parent):
        if candidate.exists() and candidate not in out:
            out.append(candidate)
    return out


# ---------------------------------------------------------------- the runner wrapper


@dataclass
class SandboxedRunner:
    """Wraps a subprocess runner so each attempt's command runs inside ``sandbox``.

    Delegates everything else -- prompt handling, the deadline ladder, answer parsing.
    The wrapped runner is *copied* per attempt and only the copy's ``argv`` and
    ``env`` (the allowlist) change.
    """

    inner: Any
    sandbox: Sandbox
    name: str = ""

    def __post_init__(self) -> None:
        if not self.name:
            self.name = f"sandboxed:{getattr(self.inner, 'name', 'runner')}"

    def available(self) -> bool:
        return available() and bool(self.inner.available())

    async def run_node(self, node: NodePayload) -> NodeResult:
        if not available():
            return NodeResult(status="error", evidence="bwrap is not installed; refusing to run a sandboxed worker unsandboxed")
        argv = getattr(self.inner, "argv", None)
        if argv is None:
            return NodeResult(status="error", evidence=f"{self.inner.name} runs in-process and cannot be sandboxed")
        node_file_dir = Path(node.file).resolve().parent if node.file else None
        try:
            wrapped = self.sandbox.wrap(list(argv), workdir=Path(node.workdir), node_file_dir=node_file_dir)
        except (OSError, ToolchainError) as exc:
            return NodeResult(status="error", evidence=f"bwrap: could not prepare the sandbox: {exc}")
        clone = copy.copy(self.inner)
        clone.argv = wrapped
        clone.env = self.sandbox.environment()
        return await clone.run_node(node)
