"""Compare the independent layout quantities with the repository's
scripts/compact_control_layer.allocation (imported read-only, no bytecode
written).  Run with python3 -B."""
import sys, itertools
sys.dont_write_bytecode = True
import os
REPO = os.environ["REPO"]  # a clone of CrocSwap/integer-mult-bounds
sys.path.insert(0, REPO + "/scripts")
from fractions import Fraction as F
import compact_control_layer as ccl          # repository code
from layout_sim import Params

n = mism = rej = 0
for m, W, G in itertools.product([2, 3, 4, 5, 15625], [2, 3, 4, 7, 8, 16, 58645352620000], [1, 6, 10, 22]):
    for d in list(range(1, 70)) + [100, 1000, 10**6, 10**30]:
        for K in sorted({1, 2, 3, 5, 8, 13, 64, 128, 10**6} | {max(1, d // 3)}):
            for D in sorted({1, 2, max(1, d // 2), d - 1 if d > 1 else 1, d}):
                pr = Params(m=m, W=W, d=d, D=D, K=K, G=G, beta=F(1, 1000)).derive()
                try:
                    a = ccl.allocation(d, D, K, G, m, W)
                except Exception as ex:
                    rej += 1
                    continue
                n += 1
                mine = (pr.q0, pr.qF, pr.qB, pr.Q0, pr.k0, "recursive" if D > pr.Q0 else "individual",
                        max(0, D - pr.Q0), min(D, pr.Q0), pr.H)
                theirs = (a["row_chunks"], a["front_chunks"], a["back_chunks"], a["reserved_chunks"],
                          a["recursion_depth_cap"], a["mode"], a["active_chunks"], a["preprocessed_chunks"],
                          a["compact_capacity"])
                if mine != theirs:
                    mism += 1
                    if mism < 10:
                        print("MISMATCH", (m, W, G, d, K, D), mine, theirs)
print(f"compared {n} parameter tuples with repository allocation(): {mism} mismatches, {rej} rejected by repo")
