"""Sweep the layout along the actual parameter family of the 2^-34 witness:
m = 15625, W = 58645352620000 (h = 25 complex network), c = 1/5,
epsilon = 1999/10000, beta = 1/1000, p = 2^L, d = floor(a * p^epsilon) for a
few band constants a, K = floor(d^c), G = 4 ceil(log2 p) + 6, and D at the
edges: 1, Q0, Q0+1, Q0 + m^k, d-1, d.  Recursion follows the extreme paths
plus random ones (sample mode)."""
import random, sys, time
from decimal import Decimal as Dm, getcontext
from fractions import Fraction as F
from layout_sim import Params, run_layout, Stats, LayoutFailure, K_from_c, G_from_p, iroot_floor

m, W = 15625, 58645352620000
c, eps, beta = F(1, 5), F(1999, 10000), F(1, 1000)
rng = random.Random(7)
tot = Stats(); runs = 0; rec = 0; fails = []; first_rec = None
t0 = time.time()
Ls = list(range(8, 280, 8)) + list(range(280, 320)) + list(range(320, 2001, 40)) + [3000, 4000]
for L in Ls:
    p = 1 << L
    for a in (F(1, 2), F(1), F(2)):
        # d = floor(a * p^eps), evaluated with 1500-digit decimals; any d in
        # the band a_d p^eps <= d <= b_d p^eps is admissible, so rounding in
        # the last digit is immaterial.
        getcontext().prec = 1500
        d = int(Dm(2) ** (Dm(L * eps.numerator) / Dm(eps.denominator)) * Dm(a.numerator) / Dm(a.denominator))
        if d < 1:
            continue
        K = K_from_c(d, c); G = G_from_p(p)
        pr0 = Params(m=m, W=W, d=d, D=1, K=K, G=G, beta=beta).derive()
        Ds = {1, d, max(1, d - 1), min(d, pr0.Q0), min(d, pr0.Q0 + 1)}
        for k in range(0, 9):
            if pr0.Q0 + m ** k <= d:
                Ds |= {pr0.Q0 + m ** k, pr0.Q0 + m ** k - 1 if m ** k > 1 else pr0.Q0 + 1}
        for D in sorted(Ds):
            if not 1 <= D <= d:
                continue
            for variant in (("ceil", "after", "low"), ("strict", "before", "high")):
                pr = Params(m=m, W=W, d=d, D=D, K=K, G=G, beta=beta, pad_mode=variant[0],
                            front_rem=variant[1], carve_at=variant[2])
                st = Stats()
                try:
                    run_layout(pr, c=c, mode="sample", max_paths=4, rng=rng, stats=st, piece_sample=12)
                except LayoutFailure as ex:
                    fails.append((L, a, D, str(ex)))
                runs += 1
                if D > pr.Q0:
                    rec += 1
                    if first_rec is None:
                        first_rec = (L, str(a), d, K, G, pr.Q0)
                for k in ("nodes", "internal", "leaves", "compact_nodes", "checks"):
                    setattr(tot, k, getattr(tot, k) + getattr(st, k))
                tot.max_depth = max(tot.max_depth, st.max_depth)
print(f"family sweep: {runs} runs over log2 p in [{Ls[0]},{Ls[-1]}] ({len(Ls)} values), 3 band constants; "
      f"{rec} recursive-mode runs; first recursive (L, a, d, K, G, Q0) = {first_rec}")
print(f"nodes={tot.nodes} internal={tot.internal} leaves={tot.leaves} compact_nodes={tot.compact_nodes} "
      f"max_depth={tot.max_depth} checks={tot.checks}  ({time.time()-t0:.0f}s)")
print("failures:", len(fails))
for f_ in fails[:10]:
    print("FAIL", f_)
