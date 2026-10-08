"""Differential comparison with the repository's own audit (read-only import).

Imports scripts/audit_compact_controls.py from the clone (no file is written:
its certificate is only written under __main__) and compares, on random and
adversarial states, the full forward map S, the inverse S^{-1}, the bad
predicate and the repaired map with this directory's independent
implementation.  The repo omits the top selected bit, so the comparison is on
the low n positions (my `ideal`, not `full_ideal`).
"""
import random
import sys
from pathlib import Path

import os
REPO = Path(os.environ["REPO"])  # a clone of CrocSwap/integer-mult-bounds
sys.path.insert(0, str(REPO / 'scripts'))
import audit_compact_controls as R   # noqa: E402

from addrmaps import Params, make_program, run, run_inverse, ideal, bad  # noqa: E402
from randomized import adversarial_state  # noqa: E402


def main(samples=150, seed=99):
    rng = random.Random(seed)
    diffs = 0
    total = 0
    for f in (2, 3, 4, 6, 9):
        for G in (1, 2, 3, 5):
            for K in (G + 4, G + 6, 2 * G + 9):
                for rho in sorted({0, K - 1, rng.randrange(K)}):
                    P = Params(f, K, rho, G)
                    for late in (False, True):
                        ops = make_program(late)
                        for _ in range(samples):
                            st = adversarial_state(P, late, rng)
                            if not late:
                                st_r = {k: st[k] for k in ('t', 'x', 'y', 'b')}
                            else:
                                st_r = {k: st[k] for k in ('u', 't', 'y', 'x', 'b')}
                            mine = run(P, st, ops)
                            theirs = R.execute(st_r, P.n, K, rho, G, late=late)
                            ok = all(mine[k] == theirs[k] for k in st_r)
                            mi = run_inverse(P, st, ops)
                            ti = R.execute(st_r, P.n, K, rho, G, late=late, inverse=True)
                            ok &= all(mi[k] == ti[k] for k in st_r)
                            ok &= bool(bad(P, st, late)) == bool(R.exceptional(st_r, P.n, K, rho, G, late))
                            rep_r = R.repaired(st_r, P.n, K, rho, G, late)
                            ok &= all(ideal(P, st)[k] == rep_r[k] for k in st_r)
                            total += 1
                            if not ok:
                                diffs += 1
                                if diffs <= 3:
                                    print('DIFF', P, late, st)
    print(f"differential vs repo audit: {total} states, {diffs} disagreements")
    return diffs


if __name__ == '__main__':
    sys.exit(1 if main() else 0)
