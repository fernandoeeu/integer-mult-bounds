#!/bin/sh
# Round 4b: counterexample hunt in the batched recursive networks of
# CrocSwap/integer-mult-bounds PR 10 (62691e3), PR 11 (a97c1ba), PR 12 (35d31e3).
# Logs to logs/.  Every step < ~0.6 GB RSS and < ~10 min on one core.
#   ./run_all.sh         independent checks + negative controls
#   ./run_all.sh --own   also the PRs' own certificate/tests (non-independent)
set -u
cd "$(dirname "$0")"
REPO="${REPO:?set REPO to a clone of CrocSwap/integer-mult-bounds with PR refs fetched as prs/N}"
export PYTHONDONTWRITEBYTECODE=1
mkdir -p logs; st=0
git -C $REPO rev-parse prs/10 prs/11 prs/12 origin/main | tee logs/heads.txt
r() { log=$1; shift; echo "== $log"; nice "$@" > logs/$log 2>&1 || st=1; tail -n 3 logs/$log; }
r certs.log          python3 certs.py                 # counts, moments, guard, margins (PR10, PR12) + controls
r pivots_h3.log      python3 pivots.py 2 3            # pivot profile lemma + controlled basis, h=3 (exact)
r pivots_h4.log      python3 pivots.py 3 4            # same at h=4 (~5 min)
r corners_modp.log   python3 corners_modp.py          # corner conditions h=5,6,8 mod p (~10 min)
r bshear.log         python3 bshear.py                # end-to-end batched recursion, address level
for mu in misalign nomiddleupdate; do
  echo "== mutant $mu (must FAIL)"; nice python3 bshear.py --mut=$mu > logs/bshear_mut_$mu.log 2>&1; tail -n 1 logs/bshear_mut_$mu.log
  grep -q "SOME FAIL" logs/bshear_mut_$mu.log || st=1
done
r complex_bulk.log   python3 complex_bulk.py          # whole-residual complex identity
if [ "${1:-}" = "--own" ]; then
  for n in 10 12; do [ -d pr$n ] || { mkdir -p pr$n; git -C $REPO archive prs/$n | tar -x -C pr$n; }; done
  ( cd pr10 && python3 scripts/batched_network.py --summary && python3 -m unittest -q tests.test_batched_network ) > logs/own_pr10.log 2>&1 || st=1
  ( cd pr12 && python3 research/batched-followup/make_patch.py ) > logs/own_pr12.log 2>&1 || st=1
  tail -n 4 logs/own_pr10.log logs/own_pr12.log
fi
echo "exit status $st"; exit $st
