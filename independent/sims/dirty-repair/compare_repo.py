"""Cross-check (run only after the independent implementation existed):
compare this implementation's S, S^{-1}, bad predicate and repair with the
repository's scripts/audit_compact_controls.py on random and adversarial
states, using the repository's layouts (early: t,x,y,b; late: u,t,y,x,b).
Run with `python3 -B` so nothing is written into the read-only clone."""
import random
import sys

import os
REPO = os.environ["REPO"]  # a clone of CrocSwap/integer-mult-bounds
sys.path.insert(0, REPO + "/scripts")
import audit_compact_controls as R  # noqa: E402

from construction import (Params, Layout, build_ops, check_order, run, run_inverse,  # noqa: E402
                          ideal_T, is_bad)


def main():
    rng = random.Random(7)
    n_cmp = 0
    for (n, K, G) in ((1, 5, 1), (1, 6, 2), (2, 7, 2), (3, 9, 3), (2, 12, 3), (4, 14, 4), (5, 30, 10)):
        for rho in sorted({0, 1, K - 1, rng.randrange(K)}):
            for late in (False, True):
                P = Params(G=G, K=K, f=n + 1, rho=rho, later=late)
                order = ["u", "t", "y", "x", "b"] if late else ["t", "x", "y", "b"]
                width = {"u": n * G, "t": n * G, "b": n * G, "x": P.L, "y": P.L}
                layout = Layout(order, width)
                ops = build_ops(P, layout)
                check_order(ops, layout)
                for k in range(600):
                    st = {f: rng.getrandbits(width[f]) for f in order}
                    if k % 3 == 0:  # push digits / guards to extremes
                        for f in ("t", "u", "b"):
                            if f in st:
                                st[f] = sum(rng.choice([0, 1, P.B - 2, P.B - 1]) << (G * i) for i in range(n))
                    mine = run(ops, st, layout)
                    theirs = R.execute(st, n, K, rho, G, late=late)
                    assert mine == theirs, ("S differs", P, st)
                    assert run_inverse(ops, mine, layout) == R.execute(theirs, n, K, rho, G, late=late, inverse=True)
                    assert bool(is_bad(P, st)) == R.exceptional(st, n, K, rho, G, late)
                    assert ideal_T(P, st) == R.ideal(st, n, K, rho)
                    want = ideal_T(P, st)
                    assert R.repaired(st, n, K, rho, G, late) == want
                    n_cmp += 1
    print(f"compare_repo: {n_cmp} states, this implementation and the repository's audit agree on "
          f"S, S^-1, bad predicate, T and repair")


if __name__ == "__main__":
    main()
