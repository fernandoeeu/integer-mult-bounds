"""PR 8 (head 9454645) geometric complex network, rebuilt from
research/geometric-complex/geometric-note.tex only, and checked with the
round-1 complex checkers in lib/complexsrc (written from the PR 3 notes).

Note, section 2: n ground points, triples T of [n] in lexicographic order,
indices 0..v-1; label space F = F_2^{n+1}, extra coordinate star = n.
  D: output for S has support {T : T cap S empty}
  E: for a pair P and target S > P, support {T > P, T != S}
"For any larger requested support, take the smallest dyadic interval of
indices containing it and split at that interval's midpoint. Recursively
construct the two nonempty parts and add them. Intern equal supports, and
discard nodes not reaching any requested output."
Labels (Lemma 'Envelope labels'): D node -> coordinate space on the union of
its source triples (input -> its line); E node -> span of its triple
indicators. Schedule: section 'Tensor-stage frames and accounting'.

Usage: python3 build.py n [--frames] [--scalar] [--three] [--nostar]
  --nostar: negative control from the note (label space F_2^n, no extra
  coordinate); must fail.
"""
import sys, os, time, json
from fractions import Fraction
from itertools import combinations
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'lib', 'complexsrc'))
from circuit import Roles                       # noqa: E402
from network import Invocation, F_KEY, Z_KEY, node_key   # noqa: E402
import flevel, pr3                              # noqa: E402

HALF = Fraction(1, 2)


class GeoCircuit:
    """Circuit container compatible with lib/complexsrc: h = label dimension,
    T = triple masks over the n ground points."""

    def __init__(self, n, star=True):
        self.n = n
        self.h = n + 1 if star else n
        trip = list(combinations(range(n), 3))      # lexicographic
        self.T = [sum(1 << p for p in t) for t in trip]
        self.tidx = {t: i for i, t in enumerate(self.T)}
        self.v = len(self.T)
        self.kind, self.args, self.family, self.label = [], [], [], []
        for i in range(self.v):
            self.kind.append('in'); self.args.append(i); self.family.append('in'); self.label.append(None)
        self.outputs = []
        self.sup = [1 << i for i in range(self.v)]

    def n_nodes(self):
        return len(self.kind)

    def n_add(self):
        return sum(1 for k in self.kind if k == 'add')


def dyadic_builder(C, family):
    """Own implementation of the dyadic-interval rule, interning per circuit."""
    v = C.v
    K = 1
    while K < v:
        K *= 2
    memo = {}

    def build(idxs, lo, hi):
        # idxs sorted, nonempty, inside [lo, hi) a dyadic interval
        if len(idxs) == 1:
            return idxs[0]
        # shrink to the smallest dyadic interval containing idxs
        while True:
            mid = (lo + hi) // 2
            if idxs[-1] < mid:
                hi = mid
            elif idxs[0] >= mid:
                lo = mid
            else:
                break
        key = tuple(idxs)
        z = memo.get(key)
        if z is not None:
            return z
        left = [i for i in idxs if i < mid]
        right = [i for i in idxs if i >= mid]
        a = build(left, lo, mid)
        b = build(right, mid, hi)
        assert not (C.sup[a] & C.sup[b])
        z = len(C.kind)
        C.kind.append('add'); C.args.append((a, b)); C.family.append(family); C.label.append(None)
        C.sup.append(C.sup[a] | C.sup[b])
        memo[key] = z
        return z
    return lambda idxs: build(sorted(idxs), 0, K)


def build(n, star=True):
    C = GeoCircuit(n, star)
    T, v = C.T, C.v
    bD = dyadic_builder(C, 'D')
    bE = dyadic_builder(C, 'E')
    for si, S in enumerate(T):
        dis = [i for i, U in enumerate(T) if not (U & S)]
        C.outputs.append((bD(dis), si, HALF))
    for si, S in enumerate(T):
        pts = [p for p in range(n) if S >> p & 1]
        for a, b in combinations(pts, 2):
            P = (1 << a) | (1 << b)
            part = [i for i, U in enumerate(T) if U & P == P and i != si]
            C.outputs.append((bE(part), si, -HALF))
    prune(C)
    # labels, from the note's lemma, recomputed from supports
    for z in range(v, C.n_nodes()):
        s = C.sup[z]
        cov, com = 0, (1 << n) - 1
        x = s
        while x:
            lb = x & -x
            cov |= T[lb.bit_length() - 1]
            com &= T[lb.bit_length() - 1]
            x ^= lb
        if C.family[z] == 'D':
            C.label[z] = ('coord', cov)
        else:
            assert bin(com).count('1') == 2, 'E node without a fixed pair'
            C.label[z] = ('star', com, cov & ~com)
    return C


def prune(C):
    live = set(z for z, _, _ in C.outputs)
    stack = list(live)
    while stack:
        z = stack.pop()
        if C.kind[z] == 'add':
            for c in C.args[z]:
                if c not in live:
                    live.add(c); stack.append(c)
    remap, kind, args, fam, lab, sup = {}, [], [], [], [], []
    for z in range(C.n_nodes()):
        if C.kind[z] == 'in' or z in live:
            remap[z] = len(kind)
            kind.append(C.kind[z]); fam.append(C.family[z]); lab.append(C.label[z]); sup.append(C.sup[z])
            args.append((remap[C.args[z][0]], remap[C.args[z][1]]) if C.kind[z] == 'add' else C.args[z])
    C.kind, C.args, C.family, C.label, C.sup = kind, args, fam, lab, sup
    C.outputs = [(remap[z], t, c) for z, t, c in C.outputs]


def coefficient_check(C):
    """Exact side map: +1/2 on disjoint T, -1/2 on |T cap S| = 2, zero else;
    plus central (|S cap T|-1)/2 gives the identity."""
    T, v = C.T, C.v
    pos, neg = [0] * v, [0] * v
    fails = []
    for z, t, c in C.outputs:
        if c == HALF:
            if pos[t] & C.sup[z]: fails.append('overlap+')
            pos[t] |= C.sup[z]
        else:
            if neg[t] & C.sup[z]: fails.append('overlap-')
            neg[t] |= C.sup[z]
    for si, S in enumerate(T):
        wd = sum(1 << i for i, U in enumerate(T) if not (U & S))
        w2 = sum(1 << i for i, U in enumerate(T) if bin(U & S).count('1') == 2)
        if pos[si] != wd or neg[si] != w2:
            fails.append(('row', si))
    for j in range(4):   # (1/2)[j=0] - (1/2)[j=2] + (j-1)/2 == [j=3]
        assert HALF * (j == 0) - HALF * (j == 2) + Fraction(j - 1, 2) == (j == 3)
    return dict(ok=not fails, fails=fails[:3])


def geo_invocation(C, R, reverse=False):
    """Schedule and frames exactly as listed in the note."""
    inv = Invocation(C, R, n_center=C.n + 1)
    v = C.v
    allX = [inv.X(T) for T in range(v)]
    allY = [inv.Y(T) for T in range(v)]
    cen = list(range(2 * v, 2 * v + C.n + 1))
    nk = lambda z: node_key(C, z)
    D0, D1 = (F_KEY, Z_KEY), (F_KEY, F_KEY)
    Xt = lambda t: (F_KEY, ('line', t))
    Yt = lambda t: (F_KEY, ('tperp', t))
    if not reverse:
        # L, -J, L^-1, -R0, V, G, R0, L, J, L^-1, -G, -V
        # D0, D0, D0, D0, X_t, D1, D0, D_Uz, Y_t, D1, D1, D1
        inv.mixers('L', lambda z: D0)
        inv.injections('-J', 'Y', lambda S: D0)
        inv.mixers('Li', lambda z: D0, inverse=True)
        inv.gate('-R0', allY + cen, D0)
        inv.copies('V', 'X', Xt)
        inv.gate('G', allX + cen, D1)
        inv.gate('R0', allY + cen, D0)
        inv.mixers('Lmid', lambda z: (F_KEY, nk(z)))
        inv.injections('J', 'Y', Yt)
        inv.mixers('Li2', lambda z: D1, inverse=True)
        inv.gate('-G', allX + cen, D1)
        inv.copies('-V', 'X', lambda t: D1)
    else:
        # V, G, L, -J, L^-1, -R0, -G, -V, R0, L, J, L^-1
        # D0, D0, D0, X_t, D_{Uz^perp}, D1, D0, Y_t, D1, D1, D1, D1
        inv.copies('V', 'Y', lambda t: D0)
        inv.gate('G', allY + cen, D0)
        inv.mixers('L', lambda z: D0)
        inv.injections('-J', 'X', Xt)
        inv.mixers('Li', lambda z: (F_KEY, ('perp', nk(z))), inverse=True)
        inv.gate('-R0', allX + cen, D1)
        inv.gate('-G', allY + cen, D0)
        inv.copies('-V', 'Y', Yt)
        inv.gate('R0', allX + cen, D1)
        inv.mixers('L2', lambda z: D1)
        inv.injections('J2', 'X', lambda S: D1)
        inv.mixers('L2i', lambda z: D1, inverse=True)
    return inv


class ScalarView:
    """lib/complexsrc scalar.Motif expects h = number of ground points."""
    def __init__(self, C):
        self.__dict__.update(C.__dict__)
        self.h = C.n


def main():
    a = sys.argv[1:]
    n = int(a[0])
    star = '--nostar' not in a
    t0 = time.time()
    C = build(n, star)
    R = Roles(C)
    nD = sum(1 for f in C.family if f == 'D')
    nE = sum(1 for f in C.family if f == 'E')
    qD = sum(1 for _, _, c in C.outputs if c == HALF)
    qE = len(C.outputs) - qD
    rep = dict(n=n, label_dim=C.h, v=C.v, D_additions=nD, D_outputs=qD, E_additions=nE, E_outputs=qE,
               roles=R.n_roles, roles_eq_c_plus_q=R.n_roles == C.n_add() + len(C.outputs),
               coeff=coefficient_check(C), t=round(time.time() - t0, 1))
    print(json.dumps(rep), flush=True)
    if '--scalar' in a or '--three' in a:
        import scalar
        M = scalar.Motif(ScalarView(C), R, 'pr3')
        assert M.nc == n + 1
        print('scalar single', scalar.single_invocation(M), flush=True)
        if '--three' in a:
            print('scalar three-stage (separate banks)', scalar.three_stage(M, shared=False), flush=True)
    if '--frames' in a:
        st = next((tuple(int(x) for x in v.split('=')[1].split(',')) for v in a if v.startswith('--stages=')), (1, 2, 3))
        out = flevel.run(C, R, geo_invocation, pr3.label_space, stages=st)
        ok = True
        h, m = C.h, C.h ** 3
        for j, o in out.items():
            aa = h ** (j - 1)
            want = (R.n_roles + n + 1) * m + 2 * o['loss'] + 2 * C.v * aa * (h - 1)
            kinds = {str(k): c for k, c in o['dec_kinds'].items()}
            good = (not o['fails']) and o['n_dec'] == n + 1 and o['loss'] == (n + 1) * h and o['tot_abs'] == want
            ok &= good
            print(f'  stage {j}: fails {len(o["fails"])} dec {o["n_dec"]} loss {o["loss"]} '
                  f'sum|d| {o["tot_abs"]} expected {want} kinds {kinds}', flush=True)
            for f in o['fails'][:3]:
                print('    FAIL', f)
        print('FRAMES', 'PASS' if ok else 'FAIL')
    print('seconds', round(time.time() - t0, 1))


if __name__ == '__main__':
    main()
