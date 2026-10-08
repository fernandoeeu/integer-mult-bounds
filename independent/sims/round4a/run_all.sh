#!/usr/bin/env bash
# Round 4a: counterexample hunt in PR 9 (head cfd6a2b) and PR 13 (head 3ef246f)
# of CrocSwap/integer-mult-bounds, both on base 6e56487.  Logs in logs/.
# Reuses (copied) round3/pr7b verify_dag.cpp, net.py, controls.py and the PR 7
# DAG/demand files from round3/pr7b/work_h{10,12,28}.  Each step < 1.3 GB, < 10 min.
#   ./run_all.sh          independent checks + controls
#   ./run_all.sh --own    additionally the PRs' own verifier/tests (scratch checkouts pr9/, pr13/)
set -u
cd "$(dirname "$0")"; ROOT=$(pwd); REPO="${REPO:?set REPO to a clone of CrocSwap/integer-mult-bounds with PR refs fetched as prs/N}"
mkdir -p logs; status=0
run() { local log=$1; shift; ( "$@" ) > "$ROOT/logs/$log" 2>&1 || status=1; }
echo "== 0 pin heads, scratch checkouts"
[ "$(git -C $REPO rev-parse prs/9)" = cfd6a2baded9dba990b987934474a7721d6ca3fb ] || status=1
[ "$(git -C $REPO rev-parse prs/13)" = 3ef246fa4f69c87ebfed78376418afa9ffcad145 ] || status=1
for p in 9 13; do [ -d pr$p ] || { mkdir -p pr$p && git -C $REPO archive prs/$p | tar -x -C pr$p; }; done
# ------------------------------------------------------------------ PR 9
cd "$ROOT/pr9chk"
for h in 8 10 12 28; do [ -f w$h/demands.txt ] || { mkdir -p w$h; cp ../../round3/pr7b/work_h$h/{dag.bin,demands.txt} w$h/; }; done
g++ -std=c++17 -O2 -o verify_dag verify_dag.cpp
echo "== PR9-1 own large-first template synthesis (README rule) + independent verifier, h=10,12,28"
for h in 10 12; do run pr9_templates_h$h.log bash -c "nice python3 mytemplates.py $h w$h/demands.txt w$h/sel.bin && ./verify_dag $h w$h/dag.bin w$h/sel.bin w$h/final.bin && nice python3 mytemplates.py $h w$h/demands.txt w$h/mine_only.bin --mode mine_only && ./verify_dag $h w$h/dag.bin w$h/mine_only.bin w$h/final_mine_only.bin"; done
run pr9_templates_h28.log bash -c "nice python3 mytemplates.py 28 w28/demands.txt w28/sel.bin && ./verify_dag 28 w28/dag.bin w28/sel.bin"
tail -n 1 ../logs/pr9_templates_h28.log
echo "== PR9-2 full network (structure, F3 scalar on every basis vector, exact rational frames) on assembled DAG with new templates, h=10"
run pr9_net_h10_select.log nice python3 net.py 10 final w10/final.bin
run pr9_net_h10_mineonly.log nice python3 net.py 10 final w10/final_mine_only.bin
grep -o '"PASS": [a-z]*' ../logs/pr9_net_h10_*.log
echo "== PR9-3 negative controls"
run pr9_neg_controls.log python3 neg_controls.py
run pr9_net_controls_h8.log nice python3 controls.py 8
cat ../logs/pr9_neg_controls.log; tail -n 1 ../logs/pr9_net_controls_h8.log | cut -c1-200
# ------------------------------------------------------------------ PR 13
cd "$ROOT/pr13chk"
echo "== PR13-1 exact arithmetic from the notes (counts, weights, log bounds, gaps, guard, margins)"
run pr13_arith.log nice python3 arith.py; tail -n 1 ../logs/pr13_arith.log
echo "== PR13-2 stage-two aux roles: first gate frame D0, last D1 (round-3 schedule model), h=10,12"
run pr13_stage2_ends.log bash -c "nice python3 stage2_ends.py 10 ../pr9chk/w10/final.bin && nice python3 stage2_ends.py 12 ../../round3/pr7b/work_h12/final.bin"
grep -o '"PASS": [a-z]*' ../logs/pr13_stage2_ends.log
echo "== PR13-3 tensor level, exact Q: exit idempotent/rank/kernel/orthogonal sum (h=5); basis-lemma corners for all (a1,a3) (h=5,6,7); Schur middle block = I (h=5)"
run pr13_tensor_h5.log nice python3 tensor_frames.py 5 1
for h in 6 7; do RANGE=10000 run pr13_tensor_h${h}_range1e4.log nice python3 tensor_frames.py $h 1; done
RANGE=3 nice python3 tensor_frames.py 6 1 > ../logs/pr13_tensor_h6_range3_artifact.log 2>&1 || true   # expected FAIL: zero first-row sums (artifact)
tail -n 1 ../logs/pr13_tensor_h*.log | cut -c1-220
# ------------------------------------------------------------------ own
if [ "${1:-}" = "--own" ]; then
  echo "== OWN PR9 verify.py (C++ global pass, ~1.2 GB) and PR13 tests/script"
  (cd "$ROOT/pr9" && nice python3 research/prime-field-followup/verify.py) > logs/own_pr9_verify.log 2>&1 || status=1
  (cd "$ROOT/pr13" && nice python3 -m unittest tests.test_source_frame_network tests.test_batched_network) > logs/own_pr13_tests.log 2>&1 || status=1
  (cd "$ROOT/pr13" && nice python3 scripts/source_frame_network.py --summary) > logs/own_pr13_script.log 2>&1 || status=1
  tail -n 3 logs/own_pr9_verify.log logs/own_pr13_tests.log logs/own_pr13_script.log
fi
echo "status $status"; exit $status
