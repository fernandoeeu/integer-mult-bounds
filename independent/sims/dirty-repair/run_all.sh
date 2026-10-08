#!/usr/bin/env bash
# Reproduce every result in REPORT.md.  Each step stays under ~20 min and
# ~2 GB on one core.  Logs and JSON land in results/.
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p results
ulimit -v 2000000 || true
nice -n 10 python3 bad_fraction.py            | tee results/bad_fraction.log
for L in 0 1 2; do
  nice -n 10 timeout 1200 python3 exhaustive.py "$L" > "results/exhaustive_level$L.log"
  tail -1 "results/exhaustive_level$L.log"
done
nice -n 10 timeout 1200 python3 random_adv.py  | tee results/random_adv.log
nice -n 10 python3 -B compare_repo.py      | tee results/compare_repo.log
# optional, slower: a few 25-27 bit exhaustive sets at rho = K-1
if [ "${DEEP:-0}" = 1 ]; then
  for L in 3 4; do
    nice -n 10 timeout 1200 python3 exhaustive.py "$L" > "results/exhaustive_level$L.log"
    tail -1 "results/exhaustive_level$L.log"
  done
fi
