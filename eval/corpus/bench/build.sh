#!/usr/bin/env bash
# Rebuild the benchmark ladder from ported upstream sources.
#
# The upstream files are NOT vendored: they are a public development whose proofs are
# the answer key, and the whole point of this corpus is that the answer key is not
# reachable from a worker.  Point PCP_BENCH_SRC at a directory holding the ported
# sources (see docs/BENCHMARKS.md for the three-line Iris 4.5 port).
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd "$here/../../.." && pwd)"
src="${PCP_BENCH_SRC:-/tmp/bench/build}"
py="${PCP_PYTHON:-$repo/.venv/bin/python}"

roles() { local f="$1"; [ -f "$here/roles/$f.roles" ] || return 0
  while IFS= read -r line; do [ -n "$line" ] && printf -- '--role\n%s\n' "$line"; done < "$here/roles/$f.roles"; }

build() {
  local file="$1"; shift
  local out="$1"; shift
  echo "=== $file"
  mapfile -t roleargs < <(roles "$out")
  "$py" "$repo/eval/make_benchmark.py" "$src/$file.v" \
    --holdout "$@" \
    --out "$here/$out" \
    --reference "$repo/.pcp/reference/$out" \
    "${roleargs[@]}"
}

# --- design rungs: the invariant itself is the task -------------------------------
#
# `--persistent` is load-bearing, not decoration.  Without it the rung has a
# degenerate solution -- define the client-facing predicate as *exclusive* ownership
# of the cell instead of an invariant, and all three specifications go through with
# no interference, hence no failing CmpXchg, hence none of the prophecy-and-helping
# argument the development exists to demonstrate.  Verified: that design compiles and
# `Print Assumptions` is clean, and it dies the moment persistence is required.
# The invariant is DROPPED, not stubbed.  A stub keeps its signature, and a signature
# is a hint: `e28_inv (γ γᵥ γₕ γᵣ : gname) ...` tells the designer they need exactly
# four ghost names and of what kind, which is a large part of the ghost construction.
# Dropping is safe because no held-out specification and no given lemma mentions the
# invariant -- it is referenced only by its own definition -- so what remains is the
# value predicate and the handle, both stubbed to `True`, exactly as the specs require.

design_rwcas() {
  echo "=== rwcas (design)"
  "$py" "$repo/eval/make_benchmark.py" "$src/rwcas.v" \
    --holdout new_rwcas_spec read_spec write_spec \
    --stub-definition value --stub-definition is_rwcas \
    --drop rwcas_inv \
    --persistent is_rwcas \
    --mutable rwcasG \
    --drop requestReg --drop requestRegUR --drop extract_result \
    --drop AU_write --drop AU_read --drop write_inv --drop registry_inv \
    --drop registry --drop registered --drop writeN \
    --drop registry_update --drop registry_agree --drop linearize_writes \
    --class-fields 'rwcasG=rwcas_heapGS :: heapGS Σ' \
    --imports 'From iris.program_logic Require Import atomic.' \
    --imports 'From iris.base_logic.lib Require Import invariants.' \
    --imports 'From iris.heap_lang Require Import lang proofmode notation.' \
    --no-anonymise --strip-comments --design-notes glossary --name Rwcas \
    --out "$here/rwcas_design" --reference "$repo/.pcp/reference/rwcas_design"
}

# The ladder, in increasing order of held-out proof size.
#
# `cached_strong` is the strongly linearizable implementation from before the
# prophecy was introduced (upstream commit 251ff8b, the parent of "Make read
# non-strongly linearizable").  Its `cas_spec` is byte-identical to `cached_wf`'s and
# its `read'_spec` is roughly half the size, so the pair isolates the cost of the
# prophecy-and-helping argument from everything else in the development.
build rwcas          rwcas          new_rwcas_spec read_spec write_spec
build seqlock        seqlock        new_big_atomic_spec read_spec write_spec
build seqlockWf      seqlock_wf     new_big_atomic_spec read_spec write_spec
build CachedStrong   cached_strong  new_big_atomic_spec "read'_spec" cas_spec
build CachedWaitFree cached_wf      new_big_atomic_spec "read'_spec" cas_spec

design_seqlock() {
  echo "=== seqlock (design)"
  # Built from the *anonymised reference*, not upstream: upstream does not compile
  # against the pinned toolchain (heapG -> heapGS, and then a chain of renamed Iris
  # lemmas), while the reference provably does -- make_benchmark verified it when the
  # proof rung was built. The names stay opaque; DESIGN.md's glossary carries the
  # roles, which is what a designer actually needs.  Primed lemmas (`wp_array_copy_to'`,
  # `wp_array_copy_to_half'`) are named by their *own* pseudonyms (`x17`, `d24` --
  # see rename_map in the proof rung's reference.json); a primed identifier is
  # renamed too, never left as `ac19'`/`a25'`.
  local ref="$repo/.pcp/reference/seqlock/Mf6dd3f_reference.v"
  "$py" "$repo/eval/make_benchmark.py" "$ref" \
    --holdout bd31_spec x34_spec fc32_spec \
    --stub-definition b10 --stub-definition efd30 \
    --drop e16_inv \
    --persistent efd30 \
    --mutable fbe7 \
    --drop d5 --drop x6 --drop x9_own --drop a11_own --drop a15 \
    --drop ef12_update --drop ff13_alloc --drop c14_agree --drop x17 \
    --drop ff18_agree --drop ac19 --drop de20 --drop d24 --drop a25 \
    --drop d29 --drop e33_inv --drop cbf21 --drop af22 --drop x23 \
    --drop b26 --drop eefe27 --drop ec28 \
    --class-fields 'fbe7=x35 :: heapGS Σ' \
    --imports 'From iris.program_logic Require Import atomic.' \
    --imports 'From iris.base_logic.lib Require Import invariants.' \
    --imports 'From iris.heap_lang Require Import lang proofmode notation lib.array.' \
    --imports 'Require Import Arith ZArith ZifyClasses ZifyInst Lia.' \
    --role b10='the client-facing logical value of the structure' \
    --role e16_inv='the main invariant protecting the data structure' \
    --role efd30='the persistent handle a client holds on the structure' \
    --no-anonymise --strip-comments --design-notes glossary --name Seqlock \
    --out "$here/seqlock_design" --reference "$repo/.pcp/reference/seqlock_design"
}

design_seqlock_wf() {
  echo "=== seqlock_wf (design)"
  # Drop list computed, not hand-written: keep the program, the class, the
  # namespaces, the three design predicates and the frozen specs; drop every other
  # named declaration. `da0`/`cb1` are the zify BinOp instances -- dropping them
  # would leave their `Add Zify` lines dangling, so they stay.  `x29`/`d35` are the
  # primed array lemmas' own pseudonyms (formerly left as `wp_array_copy_to'`/`a36'`).
  local ref="$repo/.pcp/reference/seqlock_wf/M480dd7_reference.v"
  "$py" "$repo/eval/make_benchmark.py" "$ref" \
    --holdout bd42_spec x51_spec fc50_spec \
    --stub-definition b14 --stub-definition efd41 \
    --drop e28_inv \
    --persistent efd41 \
    --mutable fbe10 \
    --drop d6 --drop x7 --drop c8 --drop b9 --drop x13_own --drop a15_own \
    --drop ef16_update --drop ff17_alloc --drop c18_agree --drop bad19 --drop ba20 \
    --drop f21_update --drop bfd22_agree --drop ac23 --drop d24_inv --drop ad25_inv \
    --drop x26_inv --drop cd27 --drop x29 --drop ff30_agree \
    --drop c31 --drop de32 --drop cbf33 --drop af34 --drop d35 --drop a36 \
    --drop b37 --drop eefe38 --drop ec39 --drop d40 --drop da43 --drop c44 \
    --drop be45 --drop fc46 --drop x47 --drop fbe48 --drop x49 \
    --class-fields 'fbe10=x52 :: heapGS Σ' \
    --imports 'From iris.program_logic Require Import atomic.' \
    --imports 'From iris.base_logic.lib Require Import invariants.' \
    --imports 'From iris.heap_lang Require Import lang proofmode notation lib.array.' \
    --imports 'Require Import Stdlib.ZArith.Zquot.' \
    --imports 'Require Import Arith ZArith ZifyClasses ZifyInst Lia.' \
    --role b14='the client-facing logical value of the structure' \
    --role e28_inv='the main invariant protecting the data structure' \
    --role efd41='the persistent handle a client holds on the structure' \
    --no-anonymise --strip-comments --design-notes glossary --name SeqlockWf \
    --out "$here/seqlock_wf_design" --reference "$repo/.pcp/reference/seqlock_wf_design"
}

# The cached rungs have NO design variant, deliberately. Two of their three held-out
# results -- `read'_spec` and `cas_spec` -- are stated *in terms of* the ghost state
# they would have to invent: both take `inv e23 (read_inv γ γᵥ γₕ γᵢ γ_val l n)` as a
# hypothesis, and `read'_spec` also names `ec29_own`, `a33_own` and `c31_own`. Stub
# the invariant and the frozen statement still hands over the ghost-state plan; drop
# the ghost predicates and the frozen statement no longer typechecks. Making a design
# rung here means restating the results at the client level, which is authoring a new
# specification rather than holding out an existing one -- a benchmark decision, not
# a build step.

design_rwcas
design_seqlock
design_seqlock_wf
