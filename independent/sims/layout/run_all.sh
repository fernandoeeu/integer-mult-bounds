#!/bin/sh
# Reproduce every result of the layout counterexample hunt.  ~25 min on a
# shared 2-core machine.  Writes logs to results/.
set -e
cd "$(dirname "$0")"
mkdir -p results
export PYTHONDONTWRITEBYTECODE=1
run() { name=$1; shift; echo "== $name"; nice python3 -B "$@" > "results/$name.log" 2>&1; tail -n 6 "results/$name.log"; }
run cert_instances  cert_instances.py
run mutants         mutants.py
run sigma_check     sigma_check.py
run explicit_sim    explicit_sim.py
run family_sweep    family_sweep.py
run sweep_quick     sweep.py --quick
run sweep_full      sweep.py            # ~10 min alone
run compare_repo    compare_repo.py
