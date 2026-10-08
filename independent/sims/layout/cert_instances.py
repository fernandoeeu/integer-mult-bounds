"""Run the layout simulation on the certificate's allocation_controls instances
(values transcribed from certificates/compact-control-layer.json, which is read
only to obtain the instance parameters and the recorded outputs to compare)."""
import json, sys, time
from fractions import Fraction as F
from layout_sim import Params, run_layout, Stats, K_from_c

import os
CERT = os.path.join(os.environ["REPO"], "certificates/compact-control-layer.json")  # REPO: a clone of CrocSwap/integer-mult-bounds
cert = json.load(open(CERT))
m = cert["complex_counts"]["m"]; W = cert["complex_counts"]["Wc"]
beta = F(1, 1000); c = F(1, 5)
ok = True
for inst in cert["allocation_controls"]:
    d, D, K, G = inst["d"], inst["D"], inst["K"], inst["G"]
    assert K == K_from_c(d, c), (K, K_from_c(d, c))
    for pad_mode in ("ceil", "strict"):
      for front_rem in ("after", "before"):
        for carve_at in ("low", "high", "mid"):
          for piece_order in ("desc", "asc"):
            pr = Params(m=m, W=W, d=d, D=D, K=K, G=G, beta=beta, pad_mode=pad_mode,
                        front_rem=front_rem, carve_at=carve_at, piece_order=piece_order)
            t = time.time()
            # pieces: for D=1e30 the base-m expansion has up to 7*15624 pieces;
            # follow 2 extreme + 3 random paths through each piece.
            st = run_layout(pr, c=c, mode="sample", max_paths=3, piece_sample=40)
            mine = dict(q0=pr.q0, qF=pr.qF, qB=pr.qB, Q0=pr.Q0, k0=pr.k0,
                        active=max(D - pr.Q0, 0) if D > pr.Q0 else 0,
                        mode="recursive" if D > pr.Q0 else "individual")
            theirs = dict(q0=inst["row_chunks"], qF=inst["front_chunks"], qB=inst["back_chunks"],
                          Q0=inst["reserved_chunks"], k0=inst["recursion_depth_cap"],
                          active=inst["active_chunks"], mode=inst["mode"])
            if mine != theirs:
                ok = False
                print("MISMATCH", d, mine, theirs)
    print(f"d={d} D={D} K={K} G={G}: q0={pr.q0} qF={pr.qF} qB={pr.qB} Q0={pr.Q0} k0={pr.k0} "
          f"nodes={st.nodes} internal={st.internal} compact={st.compact_nodes} maxdepth={st.max_depth} "
          f"checks={st.checks} {st.notes} ({time.time()-t:.1f}s, last variant)")
print("certificate instances:", "all invariants hold, values match certificate" if ok else "MISMATCH")
