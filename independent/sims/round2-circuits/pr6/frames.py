"""Frame schedule check for the PR 6 bit network, both stage directions.

Source of the frames (notes/aligned-bit-construction.tex, PR 6 head):
  forward  L', J'=J R_0, L'^-1, V, L', J', L'^-1, V^-1
           frames: D_0 for the first three operations, X_{t_X} for V, graded
           D_{U_z} for the middle L', D_0 for R_0, Y_{t_Y} for J, D_1 for the
           last two operations.
  stage 2  V, L', J, R_0, L'^-1, V^-1, L', J, R_0, L'^-1 with frames
           D_0, D_0, X_{t_X}, D_1, D_{U_z^perp}, Y_{t_Y}, then D_1.
Definitions (notes/incidence-construction.tex, paired-construction.tex):
  D_U = (B(x)F) _|_ (P(x)U); D_0 = D_{0}; D_1 = D_F; X_t = D_<t>; Y_t = D_{t^perp}.
A frame is written as a pair (Bpart, Ppart) of subspaces of F = Q^h, as in
D(B',P') = (B(x)B') _|_ (P(x)P'). Data terminals (paired/incidence notes):
  X: A(x)<t> = D(<t>,<t>) -> A(x)F = D(F,F);  Y: B(x)<t> = D(<t>,0) -> Y_t.
Auxiliary roles start at label 0 = D(0,0) and must end at D_1.

Two comparators decide inclusions:
  Comb  exact combinatorial rules, valid at any h (support containment,
        one-meet orthogonality); anything it cannot decide is reported.
  Exact exact rational linear algebra in Q^h with the form I - J/9
        (small h): actual subspaces, ranks, nondegeneracy of every label and
        every residual.
"""
from fractions import Fraction as Q
from itertools import combinations

VARIANT = None   # negative controls only
D0 = ('F', '0')
D1 = ('F', 'F')


def build_schedule(G, R, stage2=False):
    """Yield (op, wires, frame). Wires: ('X',t), ('Y',t), ('r',role)."""
    v = G.v
    gates = R.gates

    def Lgates(frame_of, inverse=False):
        seq = reversed(gates) if inverse else gates
        for z, p, s, fan in seq:
            ws = [('r', p)] + ([('r', s)] if s is not None else []) + [('r', f) for f in fan]
            yield ws, frame_of(z)

    tid = {t: k for k, t in enumerate(G.trip)}
    per_target = {}
    for k, (z, i, T) in enumerate(G.partial):
        per_target.setdefault(tid[tuple(T)], []).append(R.part_role[k])

    def Jgates(bank, frame_of):
        for t in range(v):
            yield [(bank, t)] + [('r', r) for r in per_target[t]], frame_of(t)

    def R0gates(bank, frame):
        for k, (z, i) in enumerate(G.center):
            ws = [('r', R.cen_role[k])] + [(bank, t) for t, tr in enumerate(G.trip) if i in tr]
            yield ws, frame

    def Vgates(bank, frame_of):
        for t in range(v):
            yield [(bank, t), ('r', R.src[t])], frame_of(t)

    U = lambda z: ('F', ('U', z))
    Up = lambda z: ('F', ('Up', z))
    Xt = lambda t: ('F', ('U', t))        # X_t = D_<t>; input node t has U = <t_t>
    Yt = lambda t: ('F', ('Up', t))       # Y_t = D_{t^perp}
    if not stage2:
        yield from (('L1',) + g for g in Lgates(lambda z: D0))
        yield from (('R0a',) + g for g in R0gates('Y', D0))
        yield from (('Ja',) + g for g in Jgates('Y', lambda t: D0))
        yield from (('L1inv',) + g for g in Lgates(lambda z: D0, True))
        yield from (('V',) + g for g in Vgates('X', Xt))
        yield from (('Lmid',) + g for g in Lgates(U))
        if VARIANT == 'J_before_R0':
            yield from (('Jb',) + g for g in Jgates('Y', Yt))
            yield from (('R0b',) + g for g in R0gates('Y', D0))
        else:
            yield from (('R0b',) + g for g in R0gates('Y', D0))
            yield from (('Jb',) + g for g in Jgates('Y', Yt))
        yield from (('Llate_inv',) + g for g in Lgates(lambda z: D1, True))
        yield from (('Vinv',) + g for g in Vgates('X', lambda t: D1))
    else:
        yield from (('V',) + g for g in Vgates('Y', lambda t: D0))
        yield from (('L1',) + g for g in Lgates(lambda z: D0))
        yield from (('Ja',) + g for g in Jgates('X', Xt))
        yield from (('R0a',) + g for g in R0gates('X', D1))
        yield from (('Lmid_inv',) + g for g in Lgates(U if VARIANT == 'stage2_uncomplemented' else Up, True))
        yield from (('Vinv',) + g for g in Vgates('Y', Yt))
        yield from (('L2',) + g for g in Lgates(lambda z: D1))
        yield from (('Jb',) + g for g in Jgates('X', lambda t: D1))
        yield from (('R0b',) + g for g in R0gates('X', D1))
        yield from (('L2inv',) + g for g in Lgates(lambda z: D1, True))


class Comb:
    """Exact combinatorial inclusion rules for the P (and B) parts."""

    def __init__(self, G, cm, rep, conv, center_nodes, center_dim):
        self.G, self.cm, self.rep, self.conv = G, cm, rep, conv
        self.center_dim = center_dim      # node -> exact dim (from exact LA)
        self.undecided = []
        tmask = G.tmask
        self.tmask = tmask
        self._sz = {}

    def supp_in(self, x, y):
        """support(x) subset support(y)? exact."""
        if x == y:
            return True
        cmy = self.cm[y]
        c = (cmy & -cmy).bit_length() - 1
        mx = self.conv(x, c)
        if mx is None:
            return False
        return mx & ~self.rep[y][1] == 0

    def one_meet(self, z, t):
        """every triple S of z has |S cap T| = 1 (<=> U_z in t_T^perp)."""
        c, m = self.rep[z]
        T = self.tmask[t]
        while m:
            lb = m & -m
            m ^= lb
            a, b = self.G.gpair[lb.bit_length() - 1]
            S = (1 << c) | (1 << a) | (1 << b)
            if (S & T).bit_count() != 1:
                return False
        return True

    def leq(self, a, b):
        """Exact a subset b for P-part keys; None if undecided."""
        if a == b or a == '0' or b == 'F':
            return True
        if a == 'F' or b == '0':
            return False
        ka, kb = a[0], b[0]
        if ka == 'U' and kb == 'U':
            if self.supp_in(a[1], b[1]):
                return True
            return None
        if ka == 'Up' and kb == 'Up':
            if self.supp_in(b[1], a[1]):
                return True
            return None
        if ka == 'U' and kb == 'Up':
            # U_x in U_y^perp ; only used with x an input line <t>
            # U_x in U_y^perp  <=>  B(t_S, t_T) = |S cap T| - 1 = 0 for all
            # S in supp(x), T in supp(y); decided when one side is a line.
            if b[1] < self.G.v:
                return self.one_meet(a[1], b[1])
            if a[1] < self.G.v:
                return self.one_meet(b[1], a[1])
            return None
        return None

    def dim(self, key):
        if key == '0':
            return 0
        if key == 'F':
            return self.G.h
        k, z = key
        d = self.center_dim.get(z)
        if d is None:
            return None
        return d if k == 'U' else self.G.h - d


class Exact:
    """Exact subspaces of Q^h with form B(x,y) = x.y - (sum x)(sum y)/9."""

    def __init__(self, G, sup):
        self.G, self.h = G, G.h
        self.sup = sup
        self.cache = {}

    def vec(self, t):
        x = [Q(0)] * self.h
        for p in self.G.trip[t]:
            x[p] = Q(1)
        return x

    @staticmethod
    def rref(vs, h):
        rows = []
        for v in vs:
            v = list(v)
            for r in rows:
                p = next(j for j in range(h) if r[j] != 0)
                if v[p] != 0:
                    f = v[p] / r[p]
                    v = [x - f * y for x, y in zip(v, r)]
            if any(v):
                rows.append(v)
        return rows

    def form(self, x, y):
        return sum(a * b for a, b in zip(x, y)) - sum(x) * sum(y) / 9

    def perp(self, basis):
        h = self.h
        rows = [[u[j] - sum(u) / 9 for j in range(h)] for u in basis]
        # null space of rows
        m = [list(r) for r in self.rref(rows, h)]
        piv = []
        for r in m:
            p = next(j for j in range(h) if r[j] != 0)
            piv.append(p)
        # full reduce
        for i, (r, p) in enumerate(zip(m, piv)):
            m[i] = [x / r[p] for x in r]
        for i in range(len(m)):
            for k in range(len(m)):
                if k != i and m[k][piv[i]] != 0:
                    f = m[k][piv[i]]
                    m[k] = [x - f * y for x, y in zip(m[k], m[i])]
        free = [j for j in range(h) if j not in piv]
        out = []
        for f in free:
            x = [Q(0)] * h
            x[f] = Q(1)
            for r, p in zip(m, piv):
                x[p] = -r[f]
            out.append(x)
        return out

    def space(self, key):
        sp = self.cache.get(key)
        if sp is not None:
            return sp
        h = self.h
        if key == '0':
            sp = []
        elif key == 'F':
            sp = [[Q(int(i == j)) for j in range(h)] for i in range(h)]
        elif key[0] == 'U':
            sp = self.rref([self.vec(t) for t in self.sup[key[1]]], h)
        elif key[0] == 'Up':
            sp = self.rref(self.perp(self.space(('U', key[1]))), h)
        self.cache[key] = sp
        return sp

    def rank(self, vs):
        return len(self.rref(vs, self.h))

    def nondeg(self, basis):
        if not basis:
            return True
        G = [[self.form(a, b) for b in basis] for a in basis]
        # determinant by elimination
        n = len(G)
        M = [list(r) for r in G]
        for c in range(n):
            p = next((r for r in range(c, n) if M[r][c] != 0), None)
            if p is None:
                return False
            M[c], M[p] = M[p], M[c]
            for r in range(c + 1, n):
                f = M[r][c] / M[c][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
        return True

    def posdef(self, basis):
        G = [[self.form(a, b) for b in basis] for a in basis]
        n = len(G)
        M = [list(r) for r in G]
        for c in range(n):
            if M[c][c] <= 0:
                return False
            for r in range(c + 1, n):
                f = M[r][c] / M[c][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
        return True

    def leq(self, a, b):
        A, B = self.space(a), self.space(b)
        return self.rank(A + B) == len(B)

    def dim(self, key):
        return len(self.space(key))

    def residual_nondeg(self, a, b):
        """a subset b: residual b cap a^perp is nondegenerate."""
        A, B = self.space(a), self.space(b)
        if not A:
            return self.nondeg(B), len(B)
        # residual = vectors of B orthogonal to A
        # solve: x = sum c_k B_k with form(x, A_j) = 0
        h = self.h
        rows = [[self.form(bk, aj) for bk in B] for aj in A]
        k = len(B)
        m = self.rref(rows, k) if rows else []
        piv = [next(j for j in range(k) if r[j] != 0) for r in m]
        for i, (r, p) in enumerate(zip(m, piv)):
            m[i] = [x / r[p] for x in r]
        for i in range(len(m)):
            for t in range(len(m)):
                if t != i and m[t][piv[i]] != 0:
                    f = m[t][piv[i]]
                    m[t] = [x - f * y for x, y in zip(m[t], m[i])]
        free = [j for j in range(k) if j not in piv]
        res = []
        for f in free:
            c = [Q(0)] * k
            c[f] = Q(1)
            for r, p in zip(m, piv):
                c[p] = -r[f]
            res.append([sum(c[q] * B[q][j] for q in range(k)) for j in range(h)])
        return self.nondeg(res), len(res)


def check(G, R, cmp, stage2=False, exact=None, centers=None):
    """Walk every wire; return report. cmp: Comb or Exact. If exact is also
    given (small h), every transition decided by cmp is re-decided by exact."""
    v = G.v
    cur = {}
    for t in range(v):
        cur['X', t] = (('U', t), ('U', t))
        cur['Y', t] = (('U', t), '0')
    fails, decs, und = [], [], []
    trans = {}
    cen_roles = set(R.cen_role)
    first = {}

    def cmp_pair(a, b, wire):
        ups = [cmp.leq(pa, pb) for pa, pb in zip(a, b)]
        if None in ups:
            und.append((wire, a, b, 'up'))
            return None
        if all(ups):
            return [(True, None) for _ in ups]
        downs = [cmp.leq(pb, pa) for pa, pb in zip(a, b)]
        if None in downs:
            und.append((wire, a, b, 'down'))
            return None
        return list(zip(ups, downs))

    n_edges = 0
    for op, wires, fr in build_schedule(G, R, stage2):
        for w in wires:
            old = cur.get(w, ('0', '0'))
            if w not in cur and w[0] == 'r':
                first[w] = fr
            cur[w] = fr
            if old == fr:
                continue
            n_edges += 1
            key = (old, fr)
            r = trans.get(key)
            if r is None:
                r = cmp_pair(old, fr, w)
                if r is None:
                    continue
                if exact is not None:
                    for (pa, pb), (u, d) in zip(zip(old, fr), r):
                        eu = exact.leq(pa, pb)
                        ed = exact.leq(pb, pa) if d is not None else None
                        if eu != u or (d is not None and ed != d):
                            fails.append(('comb/exact disagree', w, pa, pb, (u, d), (eu, ed)))
                trans[key] = r
            ups = [u for u, d in r]
            downs = [d for u, d in r]
            if all(ups):
                continue
            if all(downs):
                decs.append((op, w, old, fr))
                continue
            fails.append(('incomparable or mixed', op, w, old, fr))
    # endpoints
    for t in range(v):
        if cur['X', t] != D1:
            fails.append(('X sink', t, cur['X', t]))
        if cur['Y', t] != ('F', ('Up', t)):
            fails.append(('Y sink', t, cur['Y', t]))
    nonD0first = sum(1 for w, f in first.items() if f != D0)
    notD1last = 0
    for r in range(R.n_roles):
        if cur.get(('r', r)) != D1:
            notD1last += 1
    # decreases: classify and measure
    loss = 0
    dec_center = 0
    dec_other = []
    for op, w, old, fr in decs:
        d_old = cmp.dim(old[1])
        d_new = cmp.dim(fr[1])
        if old[0] != fr[0]:
            dec_other.append((op, w, old, fr, 'B part decreases'))
            continue
        if d_old is None or d_new is None:
            dec_other.append((op, w, old, fr, 'dimension unknown'))
            continue
        if exact is not None:
            if exact.dim(old[1]) != d_old or exact.dim(fr[1]) != d_new:
                fails.append(('dim mismatch', w, old, fr))
        loss += d_old - d_new
        if w[0] == 'r' and w[1] in cen_roles:
            dec_center += 1
        else:
            dec_other.append((op, w, old, fr, 'non-center decrease'))
    return dict(fails=fails, undecided=und, n_dec=len(decs), dec_center=dec_center,
                dec_other=dec_other, loss=loss, n_edges=n_edges,
                first_not_D0=nonD0first, last_not_D1=notD1last,
                transitions=trans, dec_list=decs)
