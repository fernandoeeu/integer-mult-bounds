#!/usr/bin/env bash
# Reproduce every result in REPORT.md.
#   ./run_all.sh          quick tier (small h, ~10 min on one core)
#   ./run_all.sh --full   adds the claimed sizes (PR3 h=25, PR4 h=24) and the
#                         tensor-level checks (~70 min total, each step <25 min,
#                         peak RSS < 1.5 GB)
#   ./run_all.sh --own    additionally runs each PR's own Python in
#                         checkouts/ (git archive of refs prs/3, prs/4)
set -u
cd "$(dirname "$0")"
OUT=results; mkdir -p "$OUT"
FULL=0; OWN=0
for a in "$@"; do [ "$a" = --full ] && FULL=1; [ "$a" = --own ] && OWN=1; done
run() { local name=$1; shift; echo "=== $name: $*"; nice python3 "$@" 2>&1 | tee "$OUT/$name.txt"; }

run f2selftest      steps/step_f2selftest.py
run pr3_counts      steps/step_pr3_counts.py 7 8 9 10 11 12
run pr3_flevel      steps/step_pr3_flevel.py 7 8 9 10 11 12
run pr3_scalar      steps/step_scalar.py pr3 7 8 9 10 --three
run pr4_counts      steps/step_pr4_counts.py 8 10 12
run pr4_flevel      steps/step_pr4_flevel.py 8 10 12
run pr4_halfsplit   steps/step_pr4_halfsplit.py
run pr4_scalar      steps/step_scalar.py pr4 8 10 --three
run sharing         steps/step_sharing.py
run phase           steps/step_phase.py
run params          steps/step_params.py
run pr3_h24_compare steps/step_pr3_h24_compare.py
run controls        steps/step_controls.py
if [ $FULL = 1 ]; then
  run pr3_counts_h25  steps/step_pr3_counts.py 25 --coeff
  run pr4_counts_h24  steps/step_pr4_counts.py 24 --coeff
  run big_scalar_map  steps/step_big.py
  run pr3_flevel_h25  steps/step_pr3_flevel.py 25
  run pr4_flevel_h24  steps/step_pr4_flevel.py 24
  run pr3_tensor_h7   steps/step_tensor.py pr3 7 1.0
  run pr4_tensor_h8   steps/step_tensor.py pr4 8 0.25
fi
if [ $OWN = 1 ]; then
  for p in 3 4; do
    d=checkouts/pr$p; rm -rf "$d"; mkdir -p "$d"
    git -C "${REPO:?set REPO to a clone of CrocSwap/integer-mult-bounds with PR refs fetched as prs/N}" archive prs/$p | tar -x -C "$d"
  done
  (cd checkouts/pr3 && nice python3 scripts/complex_network.py && nice python3 -m unittest tests.test_complex_network -v) 2>&1 | tee "$OUT/pr3_own.txt"
  (cd checkouts/pr4 && nice python3 scripts/retained_complex.py && nice python3 -m unittest tests.test_retained_complex -v) 2>&1 | tee "$OUT/pr4_own.txt"
fi
echo "done; outputs in $OUT/"
