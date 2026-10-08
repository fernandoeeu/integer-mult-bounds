#!/bin/sh
# Reproduce every result in REPORT.md.  Writes only to ./out/.
# Expected total time: about 15 minutes on an idle 2-core machine, about 40
# minutes when shared (exhaustive.py dominates; it runs in two halves).  Peak memory well under 1 GB.
set -e
cd "$(dirname "$0")"
mkdir -p out
nice python3 structure_params.py | tee out/structure_params.txt
nice python3 readings.py        | tee out/readings.txt
nice python3 compare_repo.py    | tee out/compare_repo.txt
nice python3 -c "import randomized as R, sys; sys.exit(1 if R.main(samples=200) else 0)" | tee out/randomized.txt
nice python3 exhaustive.py 1    | tee out/exhaustive_part1.txt
nice python3 exhaustive.py 2    | tee out/exhaustive_part2.txt
nice python3 minimal_repro.py   | tee out/minimal_repro.txt
echo "ALL DONE"
