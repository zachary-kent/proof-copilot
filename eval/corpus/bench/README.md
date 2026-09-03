# Benchmark corpora

Derived from [bigatomic-mechanization][repo] (MIT). Each directory holds a
development with its main specifications **held out** and its identifiers
anonymised — see [`docs/BENCHMARKS.md`](../../../docs/BENCHMARKS.md).

[repo]: https://github.com/cmuparlay/bigatomic-mechanization

What is here, and what is deliberately not:

- `<rung>/M*.v` — the development, with the held-out proofs replaced by `Admitted.`
  Everything else the original had is present: implementation, invariants, ghost
  state, helper lemmas. The design is *given*; the tactic work is not.
- `<rung>/DESIGN.md` — the design brief handed to every worker: the statements to
  prove, a glossary of the given definitions, and the author's own design notes.
- `<rung>/bench.json` — which proofs were held out, their size, and the anonymisation
  map. It records a **hash** of each reference proof, never the proof.
- `roles/*.roles` — human annotations that make the glossary readable.
- `build.sh` — regenerates everything from ported upstream sources.

**The reference proofs are not here and must never be.** `build.sh` writes them to
`.pcp/reference/`, which is gitignored and is masked out of every worker sandbox. A
corpus that ships its own answer key measures nothing.

The upstream sources are not vendored either: they are one `git clone` away, and
keeping them out means a worker that somehow escapes its sandbox still does not find
the answer sitting in the repo it is working in.
