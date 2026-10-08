"""PR 7 complex side: take ONLY the addition DAG and the injected pieces from
PR 7's PairedComplex (scratch checkout ../pr7/scripts), recompute every support,
cover, label and coefficient here, and hand the result to the round-1
complex checkers (lib/complexsrc: Roles, flevel, scalar), which were written
from the PR 3 notes and never import PR code.

Usage: python3 adapter.py H [--frames] [--scalar] [--three]
"""
import sys, os, time, json
from fractions import Fraction
from itertools import combinations
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'lib', 'complexsrc'))
PR7 = os.path.join(HERE, '..', 'pr7', 'scripts')

from circuit import Circuit, Roles   # noqa: E402


def their_dag(h):
    sys.path.insert(0, PR7)
    from paired_complex import PairedComplex
    c = PairedComplex(h)
    sys.path.remove(PR7)
    return c


def convert(c, h):
    """Rebuild a Circuit from (args, kinds, pieces) only. Node supports,
    point covers and labels are recomputed from scratch here."""
    C = Circuit(h)
    T = C.T                      # triple masks, lexicographic
    # their input node for triple index i is node i+1 with triple c.triples[i]
    mine = {}
    for i, t in enumerate(c.triples):
        m = sum(1 << p for p in t)
        assert T[i] == m
        mine[i + 1] = i
    sup = {i: 1 << i for i in range(C.v)}      # node -> mask over triples
    fails = []
    for n in sorted(c.active):
        if c.args[n] is None:
            continue
        a, b = c.args[n]
        za, zb = mine[a], mine[b]
        if sup[za] & sup[zb]:
            fails.append(('overlap', n))
        s = sup[za] | sup[zb]
        # recompute cover and family-specific label
        cov = 0
        x = s
        while x:
            lb = x & -x
            cov |= T[lb.bit_length() - 1]
            x ^= lb
        common = (1 << h) - 1
        x = s
        while x:
            lb = x & -x
            common &= T[lb.bit_length() - 1]
            x ^= lb
        if c.kind[n] == 'd0':
            label = ('coord', cov)
        else:
            if common.bit_count() != 2:
                fails.append(('star node without common pair', n))
            lam = cov & ~common
            label = ('star', common, lam)
        z = C.add(za, zb, c.kind[n], label)
        sup[z] = s
        mine[n] = z
    for S, node, coef in c.pieces:
        Sm = sum(1 << p for p in S)
        C.outputs.append((mine[node], C.tidx[Sm], Fraction(coef)))
    return C, sup, fails


def coefficient_check(C, sup):
    """Exact: (1/2)*disjoint - (1/2)*intersection-two, piece by piece, as
    disjoint unions of 0/1 supports (additions were checked disjoint)."""
    h, T, v = C.h, C.T, C.v
    pos = [0] * v
    neg = [0] * v
    fails = []
    for z, t, c in C.outputs:
        if c == Fraction(1, 2):
            if pos[t] & sup[z]:
                fails.append(('pos overlap', t))
            pos[t] |= sup[z]
        elif c == Fraction(-1, 2):
            if neg[t] & sup[z]:
                fails.append(('neg overlap', t))
            neg[t] |= sup[z]
        else:
            fails.append(('coef', c))
    nnz = 0
    for si, S in enumerate(T):
        wd = sum(1 << ti for ti, U in enumerate(T) if not (S & U))
        w2 = sum(1 << ti for ti, U in enumerate(T) if (S & U).bit_count() == 2)
        if pos[si] != wd:
            fails.append(('disjoint part', si))
        if neg[si] != w2:
            fails.append(('pair part', si))
        nnz += wd.bit_count() + w2.bit_count()
    # piece admissibility: every piece leaves an outside point uncovered,
    # and every piece's triples meet S evenly (label in t_S^perp)
    bad_cover = 0
    bad_even = 0
    for z, t, c in C.outputs:
        S = T[t]
        x = sup[z]
        cov = 0
        while x:
            lb = x & -x
            U = T[lb.bit_length() - 1]
            cov |= U
            if (U & S).bit_count() % 2:
                bad_even += 1
            x ^= lb
        if (cov | S) == (1 << h) - 1:
            bad_cover += 1
    return dict(ok=not fails and not bad_cover and not bad_even, nnz=nnz,
                fails=fails[:5], full_cover_pieces=bad_cover, odd_meet=bad_even)


def main():
    args = sys.argv[1:]
    h = int(args[0])
    t0 = time.time()
    c = their_dag(h)
    rep = dict(h=h, their_stats=c.stats(), t_build=round(time.time() - t0, 1))
    C, sup, fails = convert(c, h)
    rep['convert_fails'] = fails[:5]
    rep['additions'] = C.n_add()
    rep['pieces'] = len(C.outputs)
    rep['disjoint_additions'] = sum(1 for f in C.family if f == 'd0')
    rep['star_additions'] = sum(1 for f in C.family if f == 'd2')
    rep['duplicate_supports_within_family'] = (
        len([1 for z in range(C.v, C.n_nodes())]) -
        len({(C.family[z], sup[z]) for z in range(C.v, C.n_nodes())}))
    R = Roles(C)
    rep['roles'] = R.n_roles
    rep['roles_eq_c_plus_q'] = R.n_roles == C.n_add() + len(C.outputs)
    rep['coeff'] = coefficient_check(C, sup)
    print(json.dumps(rep), flush=True)
    if '--scalar' in args or '--three' in args:
        import scalar
        M = scalar.Motif(C, R, 'pr3')
        print('scalar single', scalar.single_invocation(M), flush=True)
        if '--three' in args:
            print('scalar three-stage (shared banks, pi = partner flip)',
                  scalar.three_stage(M, shared=True), flush=True)
    if '--frames' in args:
        import flevel, recipes, pr3
        out = flevel.run(C, R, recipes.pr3_invocation, pr3.label_space)
        ok = True
        for j, o in out.items():
            kinds = {str(k): n for k, n in o['dec_kinds'].items()}
            print('  stage', j, 'fails', len(o['fails']), 'dec', o['n_dec'], 'loss', o['loss'],
                  'kinds', kinds, flush=True)
            a = h ** (j - 1)
            want = (R.n_roles + h + 1) * h ** 3 + 2 * o['loss'] + 2 * C.v * a * (h - 1)
            print('    sum|d| =', o['tot_abs'], 'expected (R+h+1)m+2loss+2va(h-1) =', want, flush=True)
            ok &= (not o['fails']) and o['n_dec'] == h + 1 and o['loss'] == h * (h + 1) and o['tot_abs'] == want
        print('FRAMES', 'PASS' if ok else 'FAIL')
    print('seconds', round(time.time() - t0, 1))


if __name__ == '__main__':
    main()
