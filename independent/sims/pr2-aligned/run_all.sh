#!/usr/bin/env bash
# Reproduces every result in REPORT.md. Logs go to out/logs/.
# Usage: ./run_all.sh            (everything except the PR's own Python tests)
#        ./run_all.sh --pr-tests (also run the PR's test_aligned_paired_network.py, ~5 min)
set -u
cd "$(dirname "$0")"
mkdir -p out/logs out/graphs out/export
status=0
step() { echo "== $1"; }

step "0. literal check: complete root pairs agree across groups (aligned labelling)"
nice bun src/rootPairs.ts > out/logs/root-pairs.log 2>&1 || status=1
tail -1 out/logs/root-pairs.log

step "1. even h = 6..48: local circuit, pi, merged graph (base, aligned/support, aligned/star)"
nice bun --smol src/main.ts --h=6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48 --dump=out/graphs > out/logs/small-h.log 2>&1 || status=1
grep -E "OVERALL" out/logs/small-h.log

step "2. h = 50, one process per mode (keeps RSS near 2 GB)"
for mode in base:support aligned:star aligned:support; do
  nice bun --smol src/main.ts --h=50 --modes=$mode --export=out/export > out/logs/h50-${mode/:/-}.log 2>&1 || status=1
  grep -E "=> |OVERALL" out/logs/h50-${mode/:/-}.log | sed -E 's/ topo=.*=> / ... => /'
done

step "3. negative control (must FAIL): star key with the fixed pair dropped, h = 8"
if nice bun src/main.ts --h=8 --modes=aligned:mutant > out/logs/mutant.log 2>&1; then echo "control did NOT fail"; status=1; else echo "control failed as expected"; fi

step "4. exact rational linear algebra on frames, h = 6, 8, 10"
nice python3 -I la_check.py out/graphs/h6-*.json out/graphs/h8-*.json out/graphs/h10-*.json > out/logs/la.log 2>&1 || status=1
tail -1 out/logs/la.log

step "5. node-by-node comparison with the PR's Python graph (prs/2), h = 6..12 and 50"
rm -rf scratch/pr2 && mkdir -p scratch/pr2
git -C "${REPO:?set REPO to a clone of CrocSwap/integer-mult-bounds with PR refs fetched as prs/N}" archive prs/2 | tar -x -C scratch/pr2
for h in 6 8 10 12; do nice python3 compare_pr.py scratch/pr2 out/graphs/h$h-aligned-support.json $h; done > out/logs/compare-small.log 2>&1 || status=1
nice python3 compare_pr.py scratch/pr2 out/export/h50-aligned-support.json 50 > out/logs/compare-h50.log 2>&1 || status=1
grep -c "True" out/logs/compare-small.log; cat out/logs/compare-h50.log

if [ "${1:-}" = "--pr-tests" ]; then
  step "6. the PR's own tests (second, non-independent signal)"
  (cd scratch/pr2 && nice python3 -m unittest discover -s tests -p test_aligned_paired_network.py -v) > out/logs/pr-tests.log 2>&1 || status=1
  (cd scratch/pr2 && nice python3 scripts/aligned_paired_network.py && git diff --no-index --exit-code \
     <(git -C "${REPO:?set REPO to a clone of CrocSwap/integer-mult-bounds with PR refs fetched as prs/N}" show prs/2:certificates/aligned-paired-network.json) certificates/aligned-paired-network.json) \
     > out/logs/pr-certificate.log 2>&1 || status=1
  tail -3 out/logs/pr-tests.log; tail -3 out/logs/pr-certificate.log
fi

echo "== RUN_ALL: $([ $status = 0 ] && echo PASS || echo FAIL)"
exit $status
