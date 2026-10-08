#!/usr/bin/env bash
# Reproduces every result of the round-2 circuit hunt (PR 6 head 5015011,
# PR 4 head 8c225e6). Logs go to logs/. Every step stays below ~1.5 GB RSS
# and ~25 min on one core.
#   ./run_all.sh          everything except the PRs' own Python
#   ./run_all.sh --own    additionally runs the PRs' own tests in checkouts/
set -u
cd "$(dirname "$0")"
ROOT=$(pwd)
REPO="${REPO:?set REPO to a clone of CrocSwap/integer-mult-bounds with PR refs fetched as prs/N}"
mkdir -p logs checkouts
status=0
step() { echo "== $1"; }
run() { local log=$1; shift; ( "$@" ) > "$ROOT/logs/$log" 2>&1 || status=1; }

step "0. pin heads (refs fetched as refs/remotes/prs/*)"
git -C $REPO rev-parse prs/6 prs/4 | tee logs/heads.txt
[ "$(git -C $REPO rev-parse prs/6)" = 5015011bd9a655da038910171eee9f431f4590ff ] || status=1
[ "$(git -C $REPO rev-parse prs/4)" = 8c225e619168c0141dcfcba3b68a65bbed6a8729 ] || status=1

# ------------------------------------------------------------------ PR 6
cd "$ROOT/pr6"
step "PR6-1. even h = 8..30: supports, brute force (h<=16), roles, F_2 schedule incl. every basis vector, frames (combinatorial)"
run pr6_small.log nice python3 run.py 8 10 12 14 16 18 20 22 24 26 28 30 --basis --pi
tail -1 ../logs/pr6_small.log
step "PR6-2. exact rational frames (Q^h, form I-J/9) at h = 8, 10, 12, plus three-stage exchange with shared banks (h = 8, 10)"
run pr6_exact.log nice python3 run.py 8 10 --exact --three --basis --pi
run pr6_exact12.log nice python3 run.py 12 --exact --pi
tail -1 ../logs/pr6_exact.log; tail -1 ../logs/pr6_exact12.log
step "PR6-3. h = 36, 40, 44, 48 (combinatorial frames)"
run pr6_mid.log nice python3 run.py 36 40 44 48 --pi
tail -1 ../logs/pr6_mid.log
step "PR6-4. claimed size h = 50"
run pr6_h50.log nice python3 run.py 50 --pi
tail -1 ../logs/pr6_h50.log
step "PR6-5. negative controls (each must FAIL)"
: > ../logs/pr6_controls.log
for m in swap_output center_from_partial overlap_addition drop_center J_before_R0 stage2_uncomplemented; do
  if nice python3 run.py 8 --mutant=$m >> ../logs/pr6_controls.log 2>&1; then echo "  control $m NOT rejected"; status=1; else echo "  control $m rejected"; fi
done

# ------------------------------------------------------------------ PR 4
cd "$ROOT/pr4"
step "PR4-1. counts, totals, exact (R+J)LV = I at h = 8..14 and the claimed h = 24"
run pr4_counts.log nice python3 step_counts.py 8 10 12 14
run pr4_h24_map.log nice python3 step_counts.py 24 --map
cat ../logs/pr4_counts.log ../logs/pr4_h24_map.log
step "PR4-2. F_2 frames/residuals (both factors), three stages, h = 8..14"
run pr4_flevel.log nice python3 step_flevel.py 8 10 12 14
grep RESULT ../logs/pr4_flevel.log
step "PR4-3. F_2 frames at h = 24 (~10-20 min)"
run pr4_h24_flevel.log nice python3 step_flevel.py 24
grep RESULT ../logs/pr4_h24_flevel.log
step "PR4-4. exact dyadic scalar runs, dirty scratch, basis vectors, three-stage exchange with shared banks"
run pr4_scalar.log nice python3 step_scalar.py 8 10 --three
run pr4_scalar24.log nice python3 step_scalar.py 24
cat ../logs/pr4_scalar.log ../logs/pr4_scalar24.log
step "PR4-5. tensor-level frames on F^(x)3 at h = 8 (~7 min)"
run pr4_tensor_h8.log nice python3 step_tensor.py 8 0.25
grep -E "stage|interstage" ../logs/pr4_tensor_h8.log
step "PR4-6. phase identity on every residual pair (h = 8); stage-1/3 sharing"
run pr4_phase.log nice python3 step_phase.py 8
run pr4_sharing.log nice python3 step_sharing.py 8 24
cat ../logs/pr4_phase.log ../logs/pr4_sharing.log
step "PR4-7. negative controls"
run pr4_controls.log nice python3 step_controls.py 8
tail -1 ../logs/pr4_controls.log

# ------------------------------------------------------------- arithmetic
cd "$ROOT"
step "ARITH. exact counts, deficits, savings and windows"
run arith.log nice python3 arith.py 435346 58800 66638 24312
tail -1 logs/arith.log

# --------------------------------------------- PRs' own Python (non-independent)
if [ "${1:-}" = "--own" ]; then
  step "OWN. scratch checkouts and the PRs' own tests / generators"
  rm -rf checkouts/pr6 checkouts/pr4 && mkdir -p checkouts/pr6 checkouts/pr4
  git -C $REPO archive 5015011 | tar -x -C checkouts/pr6
  git -C $REPO archive 8c225e6 | tar -x -C checkouts/pr4
  run own_pr6_tests.log bash -c "cd checkouts/pr6 && nice python3 -m unittest tests.test_aligned_bit_network -v"
  run own_pr6_cert.log bash -c "cd checkouts/pr6 && nice python3 scripts/aligned_bit_network.py && git diff --no-index --exit-code <(git -C $REPO show 5015011:certificates/aligned-bit-network.json) certificates/aligned-bit-network.json"
  run own_pr4_tests.log bash -c "cd checkouts/pr4 && nice python3 -m unittest tests.test_retained_complex -v"
  run own_pr4_cert.log bash -c "cd checkouts/pr4 && nice python3 scripts/retained_complex.py && git diff --no-index --exit-code <(git -C $REPO show 8c225e6:certificates/retained-complex-layer.json) certificates/retained-complex-layer.json"
  tail -n 3 logs/own_pr6_tests.log logs/own_pr6_cert.log logs/own_pr4_tests.log logs/own_pr4_cert.log
  step "OWN-2. node-by-node comparison and our verifier on the PRs' graphs"
  run compare.log bash -c "for h in 8 10 12 50; do nice python3 compare_pr.py pr6 checkouts/pr6 \$h; done; for h in 8 10 12 24; do nice python3 compare_pr.py pr4 checkouts/pr4 \$h; done"
  run theirs_pr4.log bash -c "cd pr4 && nice python3 step_theirs.py ../checkouts/pr4 8 10 12 --frames --scalar && nice python3 step_theirs.py ../checkouts/pr4 24 --map --frames"
  grep -E "COMPARE|same|PR graph|frames" logs/compare.log logs/theirs_pr4.log
fi

echo "== RUN_ALL: $([ $status = 0 ] && echo PASS || echo FAIL)"
exit $status
