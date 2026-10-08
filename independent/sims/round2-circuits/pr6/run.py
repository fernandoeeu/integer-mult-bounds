"""Driver for the PR 6 checks. Usage: python3 run.py H [H ...] [--exact] [--three]
[--basis] [--counts] [--mutant=NAME]"""
import sys
import time
import json
from fractions import Fraction as Q
from itertools import combinations
from build import Builder
import verify as V
import frames as FR


def rank_star_exact(h, i):
    """Exact rank over Q of {t_T : T contains i}: lower bound from rank mod a
    prime (rank_p <= rank_Q), upper bound from the integer functional
    f(u) = sum(u) - 3 u_i vanishing on every vector."""
    p = (1 << 61) - 1
    rows = []
    vecs = []
    for T in combinations(range(h), 3):
        if i in T:
            vecs.append([1 if j in T else 0 for j in range(h)])
    assert all(sum(u) - 3 * u[i] == 0 for u in vecs)
    piv = {}
    for u in vecs:
        u = [x % p for x in u]
        for c in sorted(piv):
            if u[c]:
                r = piv[c]
                f = u[c] * pow(r[c], -1, p) % p
                u = [(a - f * b) % p for a, b in zip(u, r)]
        nz = next((c for c in range(h) if u[c]), None)
        if nz is not None:
            piv[nz] = u
    lower = len(piv)
    upper = h - 1   # nonzero functional f vanishes on the span
    return lower, upper


def mutate(g, name):
    """Negative controls: each must be rejected."""
    g = dict(g)
    if name == 'swap_output':
        P = list(g['partial'])
        (n0, i0, T0), (n1, i1, T1) = P[0], P[1]
        P[0], P[1] = (n1, i0, T0), (n0, i1, T1)
        g['partial'] = P
    elif name == 'center_from_partial':
        C = list(g['center'])
        # feed center 0 from a partial output of group 0 (a frame-legal node)
        n = next(n for n, i, T in g['partial'] if i == 0)
        C[0] = (n, 0)
        g['center'] = C
    elif name == 'overlap_addition':
        L = list(g['left'])
        R = list(g['right'])
        R[-1] = L[-1]
        g['right'] = R
    elif name == 'drop_center':
        g['center'] = g['center'][1:]
    return g


def main():
    args = sys.argv[1:]
    hs = [int(a) for a in args if a.isdigit()]
    flags = {a.split('=')[0]: (a.split('=')[1] if '=' in a else True) for a in args if a.startswith('--')}
    overall = True
    for h in hs:
        t0 = time.time()
        b = Builder(h)
        g = b.graph()
        if '--mutant' in flags:
            if flags['--mutant'] in ('J_before_R0', 'stage2_uncomplemented'):
                FR.VARIANT = flags['--mutant']
            else:
                g = mutate(g, flags['--mutant'])
        G = V.Graph(g)
        rep = {'h': h, 'c': G.c, 'q': len(G.partial), 'centers': len(G.center)}
        try:
            cm, sp, conv, f1 = V.supports(G)
            f2 = V.check_outputs(G, cm, sp, conv) if not f1 else ['skipped']
        except Exception as e:  # a broken graph may crash the support pass
            f1, f2 = [('exception', repr(e))], []
            cm = sp = conv = None
        rep['support_fails'] = f1[:3]
        rep['output_fails'] = f2[:3]
        ok = not f1 and not f2
        if sp is not None and not f1:
            rep['duplicate_supports'] = G.n - len(set(sp))
        if h <= 16:
            bf, dup, sup = V.brute_force(G)
            rep['brute_force_fails'] = bf[:3]
            rep['brute_force_duplicates'] = dup
            ok = ok and not bf
        R = V.Roles(G)
        rep['roles'] = R.n_roles
        rep['roles_eq_c_q_h'] = R.n_roles == G.c + len(G.partial) + len(G.center)
        rep['unused_nodes'] = len(R.unused)
        ok = ok and rep['roles_eq_c_q_h'] and not R.unused and R.distinct_outputs
        if ok or '--mutant' in flags:
            sr = V.scalar_random(G, R)
            rep['scalar_random'] = sr
            ok = ok and all(sr.values())
            if '--basis' in flags and h <= 24:
                sb = V.scalar_basis(G, R)
                rep['scalar_all_basis_vectors'] = sb
                ok = ok and all(sb.values())
        if ok:
            cdim = {}
            for (n, i) in G.center:
                lo, hi = rank_star_exact(h, i)
                assert lo == hi
                cdim[n] = lo
            rep['center_dims'] = sorted(set(cdim.values()))
            comb = FR.Comb(G, cm, sp, conv, None, cdim)
            exact = None
            if '--exact' in flags:
                exact = FR.Exact(G, sup)
            for st, name in ((False, 'stage1/3 forward'), (True, 'stage2')):
                r = FR.check(G, R, comb, stage2=st, exact=exact)
                rep[name] = dict(fails=len(r['fails']), first_fail=r['fails'][:2],
                                 undecided=len(r['undecided']), first_und=r['undecided'][:2],
                                 changed_edges=r['n_edges'], decreases=r['n_dec'],
                                 center_decreases=r['dec_center'], other_decreases=r['dec_other'][:3],
                                 loss=r['loss'], loss_expected=h * (h - 1),
                                 aux_first_not_D0=r['first_not_D0'], aux_last_not_D1=r['last_not_D1'],
                                 distinct_transitions=len(r['transitions']))
                good = (not r['fails'] and not r['undecided'] and not r['dec_other']
                        and r['dec_center'] == h and r['loss'] == h * (h - 1)
                        and r['first_not_D0'] == 0 and r['last_not_D1'] == 0)
                rep[name]['ok'] = good
                ok = ok and good
                if exact is not None:
                    # nondegeneracy of every label and of every residual seen
                    bad = 0
                    seen = set()
                    for (a, bb), _ in r['transitions'].items():
                        for pa, pb in zip(a, bb):
                            for key in (pa, pb):
                                if key not in seen:
                                    seen.add(key)
                                    sp_ = exact.space(key)
                                    if not exact.nondeg(sp_):
                                        bad += 1
                            lo_, hi_ = (pa, pb) if exact.leq(pa, pb) else (pb, pa)
                            nd, _ = exact.residual_nondeg(lo_, hi_)
                            if not nd:
                                bad += 1
                    rep[name]['exact_labels_checked'] = len(seen)
                    rep[name]['exact_degenerate'] = bad
                    ok = ok and bad == 0
            if exact is not None:
                pdbad = sum(1 for z in range(G.n) if not exact.posdef(exact.space(('U', z))))
                rep['exact_U_posdef_fail'] = pdbad
                ok = ok and pdbad == 0
        if '--three' in flags and ok:
            ts = V.three_stage(G, R)
            rep['three_stage'] = ts
            ok = ok and all(ts.values())
        if '--pi' in flags:
            trip, pi = V.pi_paired(h)
            rep['pi'] = dict(bijective=sorted(pi) == list(range(len(trip))),
                             meet_one=all(len(set(trip[k]) & set(trip[pi[k]])) == 1 for k in range(len(trip))))
            ok = ok and all(rep['pi'].values())
        rep['PASS'] = ok
        rep['seconds'] = round(time.time() - t0, 1)
        overall = overall and ok
        print(json.dumps(rep, default=str))
        sys.stdout.flush()
    print('OVERALL', 'PASS' if overall else 'FAIL')
    return 0 if overall else 1


if __name__ == '__main__':
    sys.exit(main())
