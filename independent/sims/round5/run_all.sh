#!/bin/sh
# Round 5: counterexample hunt in the NEW combinations of CrocSwap/integer-mult-bounds
#   PR 14 1fa5b9a (source frames + h30 data-corner batching)
#   PR 15 a17cab3 (source frames on smaller h30 producer + full complex batching)
#   PR 16 a80f5e6 (nested controlled basis + full complex batching, h32)
# Usage: REPO=/path/to/clone ./run_all.sh [--big] [--own]
#   --big : also h=7 (m=343) profile runs (~1 min each)
#   --own : also the PRs' own scripts/tests in scratch checkouts (non-independent)
# Every step < 0.3 GB RSS, < 3 min, except --own.
set -u
: "${REPO:?set REPO to the read-only clone}"
cd "$(dirname "$0")"; ROOT=$(pwd); mkdir -p logs; st=0
export PYTHONDONTWRITEBYTECODE=1
echo "== heads"
for pair in 14:1fa5b9a9aaccbebb3eb29ac7ea55811f46464eee 15:a17cab396ce1c79c288bde9d06002cefdc0af8e6 16:a80f5e676c84b59def9791495df0655efe89a04f; do
  n=${pair%%:*}; want=${pair#*:}; got=$(git -C "$REPO" rev-parse prs/$n)
  echo "prs/$n $got"; [ "$got" = "$want" ] || { echo "HEAD MISMATCH prs/$n"; st=1; }
done | tee logs/heads.txt
r() { log=$1; shift; echo "== $log"; ( "$@" ) > "$ROOT/logs/$log" 2>&1 || st=1; tail -n 2 "$ROOT/logs/$log" | cut -c1-300; }
cd "$ROOT/pr14chk"
# one controlled basis vs all claimed pivot profiles (PR14 classes; PR16 nested family adds the diagonal exit block)
r prof_h4_ctrl.log   nice python3 profiles.py 4 2 1 6 1
r prof_h4_nest.log   nice python3 profiles.py 4 2 1 6 1 --nested
r prof_h5_ctrl.log   nice python3 profiles.py 5 3 2 6 2
r prof_h5_nest.log   nice python3 profiles.py 5 3 2 6 2 --nested
r prof_h6_ctrl.log   nice python3 profiles.py 6 3 2 4 11
r prof_h6_nest.log   nice python3 profiles.py 6 3 2 4 12 --nested
if [ "${1:-}" = "--big" ] || [ "${2:-}" = "--big" ]; then
  r prof_h7_ctrl.log nice python3 profiles.py 7 3 2 2 13
  r prof_h7_nest.log nice python3 profiles.py 7 3 2 2 14 --nested
fi
echo "== negative controls (each must print SOME FAIL)"
for a in "--mut=noS" "--mut=tensorS" "--mut=blk+1" "--claim-nested"; do
  nice python3 profiles.py 5 3 2 2 3 $a > "$ROOT/logs/prof_control_${a#--}.log" 2>&1
  if grep -q "SOME FAIL" "$ROOT/logs/prof_control_${a#--}.log"; then echo "control $a rejected (good)"; else echo "control $a NOT rejected"; st=1; fi
done
cd "$ROOT/arith";  r bit_arith.log nice python3 bit_arith.py
cd "$ROOT/pr16chk"; r complex_arith.log nice python3 complex_arith.py
git -C "$REPO" show prs/15:certificates/complex-all-residuals.json > pr15_complex.json
r cmp_hist.log nice python3 cmp_hist.py
grep -h "DISCREPANCY\|SAME" "$ROOT/logs/cmp_hist.log" | cut -c1-400
cd "$ROOT"
if [ "${1:-}" = "--own" ] || [ "${2:-}" = "--own" ]; then
  for n in 14 15 16; do [ -d pr$n ] || { mkdir -p pr$n; git -C "$REPO" archive prs/$n | tar -x -C pr$n; }; done
  ./own.sh || st=1
fi
echo "exit status $st"; exit $st
