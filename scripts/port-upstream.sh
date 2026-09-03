#!/usr/bin/env bash
# Port an upstream .v file to the pinned Iris, by iteration.
#
# Compile, read the first "The variable X was not found" error, try the frac->dfrac
# rename that Iris 4.5 introduced, and repeat.  Anything it cannot explain it reports
# rather than guessing at -- a "port" that silently changes meaning is worse than a
# failed build.
#
#   scripts/port-upstream.sh <dir> <basename-without-.v>
#
# See docs/BENCHMARKS.md for the four renames this finds in practice.
set -u
dir="${1:?usage: port-upstream.sh <dir> <module>}"
f="${2:?usage: port-upstream.sh <dir> <module>}"
cd "$dir"
: "${ROCQPATH:=$HOME/.opam/pcp/lib/coq/user-contrib}"
export PATH="$HOME/.opam/pcp/bin:$PATH" ROCQPATH
IRIS="$ROCQPATH/iris"
[ -f _CoqProject ] || echo "-Q . bench" > _CoqProject
for i in $(seq 1 40); do
  if timeout 3600 coqc -Q . bench -w -notation-overridden "$f.v" > "$f.log" 2>&1; then
    echo "$f: OK after $((i-1)) rename(s)"; exit 0
  fi
  missing=$(grep -A1 "^Error: The variable" "$f.log" | tr '\n' ' ' | sed -E 's/.*The variable ([A-Za-z0-9_.]+) was not found.*/\1/' | head -1)
  if [ -z "$missing" ]; then
    echo "$f: non-rename error:"; grep -A4 "^Error" "$f.log" | head -8; exit 1
  fi
  cand="${missing/_frac_/_dfrac_}"
  if [ "$cand" = "$missing" ] || ! grep -rqE "(Lemma|Definition|Instance|Notation) +$cand\b" "$IRIS"; then
    echo "$f: no known replacement for '$missing'"; grep -B3 -A4 "^Error" "$f.log" | head -12; exit 1
  fi
  echo "  $missing -> $cand"
  sed -i "s/\b$missing\b/$cand/g" "$f.v"
done
echo "$f: gave up after 40 iterations"; exit 1
