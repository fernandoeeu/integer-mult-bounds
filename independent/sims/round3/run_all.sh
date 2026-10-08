#!/usr/bin/env bash
# Round 3: counterexample hunt in PR 7 (head 6725c6a) and PR 8 (head 9454645)
# of CrocSwap/integer-mult-bounds.  Logs go to logs/.  Every step stays below
# ~1.2 GB RSS and ~25 min on one core (run on a shared 2-core machine).
#   ./run_all.sh          independent checks + negative controls
#   ./run_all.sh --own    additionally the PRs' own tests/verifiers (second,
#                         non-independent signal) in scratch checkouts pr7/, pr8/
set -u
cd "$(dirname "$0")"
ROOT=$(pwd)
REPO="${REPO:?set REPO to a clone of CrocSwap/integer-mult-bounds with PR refs fetched as prs/N}"
mkdir -p logs
status=0
step() { echo "== $1"; }
run() { local log=$1; shift; ( "$@" ) > "$ROOT/logs/$log" 2>&1 || status=1; }

step "0. pin heads (refs fetched as refs/remotes/prs/*), scratch checkouts by git archive"
git -C $REPO rev-parse prs/7 prs/8 | tee logs/heads.txt
[ "$(git -C $REPO rev-parse prs/7)" = 6725c6a17b17871a35353fd29157f4ed851bc114 ] || status=1
[ "$(git -C $REPO rev-parse prs/8)" = 9454645ccb61663d13dcf7cc69ade762665ae9ed ] || status=1
for p in 7 8; do [ -d pr$p ] || { mkdir -p pr$p && git -C $REPO archive prs/$p | tar -x -C pr$p; }; done

# ------------------------------------------------------------ PR 7 bit side
cd "$ROOT/pr7b"
step "PR7-B1. own producer (from the note): structure, F_3 scalar on every basis vector, three-stage exchange with pi-shared banks, exact rational frames (h=8, 10)"
run pr7b_mine_h8.log nice python3 net.py 8 mine --three
run pr7b_mine_h10.log nice python3 net.py 10 mine
tail -c 300 ../logs/pr7b_mine_h8.log; tail -c 120 ../logs/pr7b_mine_h10.log
step "PR7-B2. run PR 7's own producer pipeline (local producer, C++ merge, star templates) at h=10, 12, 28; keep its files"
for h in 10 12 28; do run pr7b_theirs_h$h.log nice python3 run_theirs.py $h; done
grep "pass 2" ../logs/pr7b_theirs_h28.log | cut -c1-400
step "PR7-B3. independent C++ verifier on their DAG files (supports, disjointness, common pair, outputs, star demand, templates, counts)"
g++ -std=c++17 -O2 -o verify_dag verify_dag.cpp
for h in 10 12; do run pr7b_verify_h$h.log ./verify_dag $h work_h$h/dag.bin work_h$h/templates.bin work_h$h/final.bin; done
run pr7b_verify_h28.log ./verify_dag 28 work_h28/dag.bin work_h28/templates.bin
cat ../logs/pr7b_verify_h10.log ../logs/pr7b_verify_h12.log ../logs/pr7b_verify_h28.log
step "PR7-B4. full network on THEIR assembled final DAG: scalar (every basis vector), exact rational frames, both orientations (h=10, 12)"
run pr7b_final_h10.log nice python3 net.py 10 final work_h10/final.bin
run pr7b_final_h12.log nice python3 net.py 12 final work_h12/final.bin --noframes
tail -c 200 ../logs/pr7b_final_h10.log; tail -c 200 ../logs/pr7b_final_h12.log
step "PR7-B5. matching pi (h = 8..28), exact retained span dimension at h=28"
run pr7b_matching.log nice python3 -c "import net,json
for h in (8,12,16,20,24,28): print(json.dumps(net.matching(h)[1]))"
run pr7b_retained_rank.log nice python3 retained_rank.py 28
cat ../logs/pr7b_matching.log ../logs/pr7b_retained_rank.log
step "PR7-B6. negative controls (each must be rejected)"
run pr7b_controls.log nice python3 controls.py 8
tail -n 1 ../logs/pr7b_controls.log

# ---------------------------------------------------------- PR 7 complex side
cd "$ROOT/pr7c"
step "PR7-C1. their PairedComplex DAG, everything recomputed: coefficients, roles, scalar (dirty), three-stage shared banks, F_2 frames (h=8,10,12)"
for h in 8 10 12; do run pr7c_h$h.log nice python3 adapter.py $h --frames --scalar $( [ $h -le 10 ] && echo --three ); done
grep -h -E "FRAMES|three" ../logs/pr7c_h8.log ../logs/pr7c_h10.log ../logs/pr7c_h12.log
step "PR7-C2. claimed size h=28 (~8-15 min)"
run pr7c_h28.log nice python3 adapter.py 28 --frames --scalar
grep -E "FRAMES|sum" ../logs/pr7c_h28.log; head -c 400 ../logs/pr7c_h28.log; echo
step "PR7-C3. tensor-level frames and phase identity (h=8); bank sharing (h=8..28)"
cd "$ROOT/lib"
run pr7c_tensor_phase_h8.log nice python3 step_tensor_phase.py pr7c 8 0.5
run pr7c_sharing.log nice python3 step_sharing_pr7c.py
tail -n 2 ../logs/pr7c_tensor_phase_h8.log; tail -n 1 ../logs/pr7c_sharing.log
cd "$ROOT/pr7c"
step "PR7-C4. negative controls"
run pr7c_controls.log nice python3 controls.py 10
tail -n 1 ../logs/pr7c_controls.log

# ------------------------------------------------------------------- PR 8
cd "$ROOT/pr8geo"
step "PR8-1. own rebuild from the note: counts, coefficients, scalar, three-stage, F_2 frames (n = 6, 7, 8)"
for n in 6 7 8; do run pr8_n$n.log nice python3 build.py $n --frames --scalar --three; done
grep -h -E "FRAMES|three" ../logs/pr8_n6.log ../logs/pr8_n7.log ../logs/pr8_n8.log
step "PR8-2. claimed size n=25: counts, coefficients, scalar; F_2 frames one stage per process"
run pr8_n25_counts.log nice python3 build.py 25 --scalar
for s in 1 2 3; do run pr8_n25_frames_s$s.log nice python3 build.py 25 --frames --stages=$s; done
head -c 300 ../logs/pr8_n25_counts.log; echo; grep -h -E "stage|FRAMES" ../logs/pr8_n25_frames_s*.log
step "PR8-3. tensor-level frames and phase identity (n = 6, 7)"
cd "$ROOT/lib"
run pr8_tensor_phase_n6.log nice python3 step_tensor_phase.py pr8 6 1.0
run pr8_tensor_phase_n7.log nice python3 step_tensor_phase.py pr8 7 0.5
tail -n 1 ../logs/pr8_tensor_phase_n6.log ../logs/pr8_tensor_phase_n7.log
cd "$ROOT/pr8geo"
step "PR8-4. negative controls (includes the note's own missing-coordinate control)"
run pr8_controls.log nice python3 controls.py 7
tail -n 1 ../logs/pr8_controls.log
step "ARITH. exact counts, savings and margins for both PRs"
cd "$ROOT"; run arith.log nice python3 arith.py; tail -n 30 logs/arith.log

# ----------------------------------------------- PRs' own code (non-independent)
if [ "${1:-}" = "--own" ]; then
  step "OWN-7. PR 7 own tests and certificate generator"
  run own_pr7_tests.log bash -c "cd pr7 && nice python3 -m unittest tests.test_prime_field_network -v"
  run own_pr7_cert.log bash -c "cd pr7 && nice python3 scripts/prime_field_network.py && git diff --no-index --exit-code <(git -C $REPO show prs/7:certificates/prime-field28.json) certificates/prime-field28.json"
  tail -n 4 logs/own_pr7_tests.log logs/own_pr7_cert.log
  step "OWN-8. PR 8: node-by-node comparison of the own rebuild with explore.Circuit; verify.py and audit.py"
  run own_pr8_compare.log bash -c "cd pr8geo && nice python3 compare_pr.py 25"
  cat logs/own_pr8_compare.log
  run own_pr8_verify.log bash -c "cd pr8 && nice python3 research/geometric-complex/verify.py"
  run own_pr8_audit.log bash -c "cd pr8 && nice python3 research/geometric-complex/audit.py > ../logs/own_pr8_audit.json && diff <(git -C $REPO show prs/8:research/geometric-complex/physical-audit.json) ../logs/own_pr8_audit.json && echo audit identical"
  tail -n 4 logs/own_pr8_verify.log logs/own_pr8_audit.log
fi
echo "== RUN_ALL: $([ $status = 0 ] && echo PASS || echo FAIL)"
exit $status
