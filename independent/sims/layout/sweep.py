"""Exhaustive small-parameter sweep of the layout invariants (symbolic mode).

For every (m, W, G, d, K) and every D in [1, d] the global claims are checked;
for every D > Q0 (recursive mode) the full recursion is simulated under every
reading of the ambiguous details.  Prints case counts and any failure.
"""
import sys, time, itertools, random
from fractions import Fraction as F
from layout_sim import Params, run_layout, Stats, LayoutFailure, K_from_c, G_from_p, ceil_log

QUICK = "--quick" in sys.argv

ms = [2, 3, 4]
Ws = [2, 3, 4, 6, 7, 16]
Gs = [1, 2, G_from_p(2)]          # free small G and as written (G(2) = 10)
betas = [F(1, 1000), F(1, 2), F(999, 1000)]
cs = [F(1, 5), F(1, 2), F(1, 1)]
dmax = 24 if QUICK else 48
Kmax = 24 if QUICK else 48
variants = list(itertools.product(["ceil", "strict"], ["after", "before"], ["low", "high", "mid"], ["desc", "asc"]))

tot = Stats()
cases = dict(global_only=0, fallback=0, recursive=0, recursive_runs=0, tied_K_recursive=0, boundary_D=0,
             exact_multiple_rows=0, stop_boundary_runs=0)
failures = []
t0 = time.time()
rng = random.Random(1)


def run(pr, c, kind):
    global failures
    try:
        st = Stats()
        n_paths = (pr.m) ** max(pr.k0, 0)
        if n_paths <= 4000:
            run_layout(pr, c=c, mode="full", stats=st)
        else:
            run_layout(pr, c=c, mode="sample", max_paths=40, rng=rng, stats=st)
        for k in ("nodes", "internal", "leaves", "compact_nodes", "checks", "boundary_nodes"):
            setattr(tot, k, getattr(tot, k) + getattr(st, k))
        tot.max_depth = max(tot.max_depth, st.max_depth)
        return st
    except LayoutFailure as ex:
        failures.append((kind, pr, str(ex)))
        return None


for m, W, G in itertools.product(ms, Ws, Gs):
    for d in range(1, dmax + 1):
        Ks = set(range(1, Kmax + 1))
        tied = {K_from_c(d, c): c for c in cs}
        for K in sorted(Ks | set(tied)):
            c = tied.get(K)
            base = Params(m=m, W=W, d=d, D=1, K=K, G=G, beta=betas[0]).derive()
            Q0 = base.Q0
            # global claims for D <= Q0 (fallback) - checked once per D range
            for D in range(1, min(d, Q0) + 1):
                cases["fallback"] += 1
            pr = Params(m=m, W=W, d=d, D=min(d, max(Q0, 1)), K=K, G=G, beta=betas[0])
            run(pr, c, "global")
            cases["global_only"] += 1
            for D in range(Q0 + 1, d + 1):
                cases["recursive"] += 1
                if c is not None:
                    cases["tied_K_recursive"] += 1
                if D == Q0 + 1:
                    cases["boundary_D"] += 1
                if (1 << (base.q0 * K)) % (W ** base.k0) == 0:
                    cases["exact_multiple_rows"] += 1
                for beta in betas:
                    vs = variants if (D in (Q0 + 1, d) and beta == F(1, 2)) else variants[:1]
                    for (pm, fr, ca, po) in vs:
                        pr = Params(m=m, W=W, d=d, D=D, K=K, G=G, beta=beta, pad_mode=pm,
                                    front_rem=fr, carve_at=ca, piece_order=po)
                        run(pr, c, "recursive")
                        cases["recursive_runs"] += 1

# explicit boundary families: d chosen so d^beta is an exact power of m
for m in ms:
    for W in [2, 3, 4, 7]:
        for beta in [F(1, 2), F(1, 3), F(2, 3)]:
            for k in range(1, 4):
                # d = m^(k/beta) when integral
                if (k * beta.denominator) % beta.numerator:
                    continue
                d = m ** (k * beta.denominator // beta.numerator)
                if d > 5000:
                    continue
                for G in [1, 2]:
                    for K in range(1, 80):
                        pr0 = Params(m=m, W=W, d=d, D=d, K=K, G=G, beta=beta).derive()
                        if pr0.Q0 >= d:
                            continue
                        for D in sorted({pr0.Q0 + 1, pr0.Q0 + m ** k, d}):
                            if not (pr0.Q0 < D <= d):
                                continue
                            for (pm, fr, ca, po) in variants[::5]:
                                pr = Params(m=m, W=W, d=d, D=D, K=K, G=G, beta=beta, pad_mode=pm,
                                            front_rem=fr, carve_at=ca, piece_order=po)
                                run(pr, None, "boundary")
                                cases["stop_boundary_runs"] += 1
                                cases["recursive_runs"] += 1

print("sweep ranges: m in", ms, "W in", Ws, "G in", Gs, f"d in [1,{dmax}]", f"K in [1,{Kmax}] plus floor(d^c) c in", [str(c) for c in cs],
      "beta in", [str(b) for b in betas], f"variants {len(variants)}")
print("case counts:", cases)
print(f"nodes={tot.nodes} internal={tot.internal} leaves={tot.leaves} compact_nodes={tot.compact_nodes} "
      f"max_depth={tot.max_depth} boundary_nodes(e=d^beta exactly)={tot.boundary_nodes} checks={tot.checks}")
print(f"failures: {len(failures)}  ({time.time()-t0:.0f}s)")
for kind, pr, msg in failures[:20]:
    print("FAIL", kind, msg, pr)
