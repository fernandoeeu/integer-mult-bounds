"""Independent small-h model of PR 7's F_3 five-subset interchange network,
written from notes/prime-field28-construction.tex (PR 7 head 6725c6a).

Graph: inputs 0..v-1 are the five-subsets of [h] in increasing mask order;
additions (a, b); outputs (node, C) where C is the common pair of the context
that requested it.  Whether an output is the retained total A_C or a side
output D_{C,E} (and its target S = C u E) is decided HERE from its exact
support, never from the producer.

Requirements checked (quoted from the PR 7 note):
 R1 "every addition is disjoint" / cancellation-free: disjoint supports
 R2 "Each retained node ... has a common pair": core size >= 2
 R3 outputs: A_C = sum_{T > C} x_T, D_{C,E} = sum_{T = C u U, U cap E = 0} x_T,
    each (C,E) and each C exactly once
 R4 scalar: "A source and target with intersection k have coefficient
    C(k,2) - [k=2] modulo three ... Thus their combined map is the identity",
    schedule "L, -R_0, -J, L^-1, V, L, R_0, J, L^-1, -V", "For arbitrary
    initial auxiliary vector z ... restores z, and changes the target by x",
    inverse gives the inverse shear; three stages + final negation exchange.
 R5 roles: "one role per addition plus one per output use"
 R6 frames (exact rational, F = Q^h, H = I - (2/25)J): both stage
    orientations, every edge between comparable nondegenerate labels, "Only
    the retained output roles decrease, from D_U to D_0, by h-2 each", same
    loss reversed, aux roles start at 0 and end at D_1.
 R7 matching pi: bijection with |T cap pi(T)| = 2.
"""
import sys, time, json
from fractions import Fraction as Q
from itertools import combinations
import numpy as np

ALPHA = Q(2, 25)
MUTANT = None   # negative controls only (see controls.py)


# ------------------------------------------------------------------ graph
class Graph:
    def __init__(self, h, adds, outputs):
        self.h = h
        self.five = [m for m in range(1 << h) if bin(m).count('1') == 5]
        self.v = len(self.five)
        self.idx = {m: i for i, m in enumerate(self.five)}
        self.adds = adds
        self.outputs = outputs          # list of (node, Cmask)
        self.n = self.v + len(adds)


def mine(h, star=False):
    """Own producer from the note's specification only: for every pair C and
    every E (|E|=3, and E empty for the total) form the requested sum by
    recursive halving of its sorted source list; intern equal supports
    globally (exact int masks)."""
    five = [m for m in range(1 << h) if bin(m).count('1') == 5]
    idx = {m: i for i, m in enumerate(five)}
    v = len(five)
    adds, intern = [], {}
    sup = [1 << i for i in range(v)]

    def build(lst):
        if len(lst) == 1:
            return lst[0]
        k = len(lst) // 2
        a, b = build(lst[:k]), build(lst[k:])
        s = sup[a] | sup[b]
        z = intern.get(s)
        if z is None:
            z = v + len(adds)
            adds.append((a, b))
            sup.append(s)
            intern[s] = z
        return z

    outputs = []
    for C in combinations(range(h), 2):
        Cm = (1 << C[0]) | (1 << C[1])
        rest = [p for p in range(h) if p not in C]
        for E in [()] + list(combinations(rest, 3)):
            Em = sum(1 << p for p in E)
            lst = [idx[Cm | sum(1 << p for p in U)] for U in combinations(rest, 3) if not (sum(1 << p for p in U) & Em)]
            outputs.append((build(lst), Cm, Cm | Em) if E else (build(lst), Cm))
    return Graph(h, adds, outputs)


def load_final(path, h):
    import struct
    data = open(path, 'rb').read()
    w = struct.unpack('<%dI' % (len(data) // 4), data)
    v, na = w[0], w[1]
    adds = [(w[2 + 2 * i], w[3 + 2 * i]) for i in range(na)]
    p = 2 + 2 * na
    nr = w[p]
    outputs = [(w[p + 1 + 2 * i], w[p + 2 + 2 * i]) for i in range(nr)]
    g = Graph(h, adds, outputs)
    assert g.v == v
    return g


# --------------------------------------------------------------- supports
def check_structure(g):
    h, v, five = g.h, g.v, g.five
    sup = [1 << i for i in range(v)]
    core = list(five)
    fails = []
    for k, (a, b) in enumerate(g.adds):
        z = v + k
        if not (a < z and b < z):
            fails.append(('topology', z))
        if sup[a] & sup[b]:
            fails.append(('overlap', z))
        sup.append(sup[a] | sup[b])
        core.append(core[a] & core[b])
        if bin(core[z]).count('1') < 2:
            fails.append(('no common pair', z))
    # outputs
    allC = {}
    for C in combinations(range(h), 2):
        Cm = (1 << C[0]) | (1 << C[1])
        allC[Cm] = sum(1 << i for i, m in enumerate(five) if m & Cm == Cm)
    kinds = []      # per output: ('A', C) or ('D', C, S)
    seen = set()
    for out in g.outputs:
        z, Cm = out[0], out[1]
        s = sup[z]
        if len(out) == 3:      # explicit target (own producer only)
            Sm = out[2]
            want = sum(1 << i for i, m in enumerate(five) if m & Sm == Cm)
            if s != want:
                fails.append(('D inexact', z))
            key = ('D', Cm, Sm)
        elif s == allC[Cm]:
            key = ('A', Cm)
        else:
            cover = 0
            x = s
            while x:
                lb = x & -x
                cover |= five[lb.bit_length() - 1]
                x ^= lb
            E = ((1 << h) - 1) & ~cover
            if bin(E).count('1') != 3 or E & Cm:
                # single-source outputs (h=8): E is not visible from the cover
                fails.append(('output neither A_C nor D_CE', z))
                kinds.append(None)
                continue
            want = sum(1 << i for i, m in enumerate(five) if m & (Cm | E) == Cm)
            if s != want:
                fails.append(('D inexact', z))
            key = ('D', Cm, Cm | E)
        if key in seen:
            fails.append(('duplicate output', key))
        seen.add(key)
        kinds.append(key)
    nA = sum(1 for k in seen if k[0] == 'A')
    nD = sum(1 for k in seen if k[0] == 'D')
    from math import comb
    if nA != comb(h, 2) or nD != comb(h, 2) * comb(h - 2, 3):
        fails.append(('output counts', nA, nD))
    unused = set(range(v, g.n)) - {a for a, b in g.adds} - {b for a, b in g.adds} - {o[0] for o in g.outputs}
    if unused:
        fails.append(('unused additions', len(unused)))
    return sup, core, kinds, fails


# -------------------------------------------------------------------- roles
class Roles:
    """Outgoing-use / pivot compiler: an input allocates one role per use; an
    addition reuses the role of its first operand edge as pivot for its first
    use and allocates one new role for every further use."""

    def __init__(self, g):
        v, n = g.v, g.n
        uses = [[] for _ in range(n)]
        for k, (a, b) in enumerate(g.adds):
            uses[a].append(('add', v + k, 0))
            uses[b].append(('add', v + k, 1))
        for o, out in enumerate(g.outputs):
            uses[out[0]].append(('out', o))
        nr = 0
        edge = {}
        self.slots = [None] * v
        self.gates = []
        for z in range(v):
            rs = list(range(nr, nr + len(uses[z])))
            nr += len(rs)
            for u, r in enumerate(rs):
                edge[z, u] = r
            self.slots[z] = rs
        for k, (a, b) in enumerate(g.adds):
            z = v + k
            piv = edge[a, uses[a].index(('add', z, 0))]
            sec = edge[b, uses[b].index(('add', z, 1))]
            edge[z, 0] = piv
            fan = list(range(nr, nr + len(uses[z]) - 1))
            nr += len(fan)
            for u, r in enumerate(fan):
                edge[z, u + 1] = r
            self.gates.append((z, piv, sec, fan))
        self.out = [None] * len(g.outputs)
        for z in range(n):
            for u, use in enumerate(uses[z]):
                if use[0] == 'out':
                    self.out[use[1]] = edge[z, u]
        self.n = nr


# ------------------------------------------------------------- F_3 scalar
class Scalar:
    def __init__(self, g, R, kinds):
        self.g, self.R = g, R
        self.inj = [[] for _ in range(g.v)]     # target -> roles (D outputs)
        self.ret = []                           # (role, [targets])
        for o, k in enumerate(kinds):
            if k[0] == 'D':
                self.inj[g.idx[k[2]]].append(R.out[o])
            else:
                Cm = k[1]
                self.ret.append((R.out[o], [i for i, m in enumerate(g.five) if m & Cm == Cm]))

    def L(self, Z, inv=False):
        gates = reversed(self.R.gates) if inv else self.R.gates
        for z, p, s, fan in gates:
            if not inv:
                Z[p] = (Z[p] + Z[s]) % 3
                for f in fan:
                    Z[f] = (Z[f] + Z[p]) % 3
            else:
                for f in fan:
                    Z[f] = (Z[f] - Z[p]) % 3
                Z[p] = (Z[p] - Z[s]) % 3

    def R0(self, Y, Z, sign):
        for r, ts in self.ret:
            Y[ts] = (Y[ts] + sign * Z[r]) % 3

    def J(self, Y, Z, sign):       # J injects  -sum D  (sign=+1)
        if MUTANT == 'J_plus':
            sign = -sign
        for S, rs in enumerate(self.inj):
            for r in rs:
                Y[S] = (Y[S] - sign * Z[r]) % 3

    def V(self, X, Z, sign):
        for t, rs in enumerate(self.R.slots):
            for r in rs:
                Z[r] = (Z[r] + sign * X[t]) % 3

    def forward(self, X, Y, Z):
        self.L(Z); self.R0(Y, Z, -1); self.J(Y, Z, -1); self.L(Z, True)
        self.V(X, Z, 1); self.L(Z); self.R0(Y, Z, 1); self.J(Y, Z, 1); self.L(Z, True); self.V(X, Z, -1)

    def inverse(self, X, Y, Z):
        """Reversed schedule with every operation inverted: Y -= X."""
        self.V(X, Z, 1); self.L(Z); self.J(Y, Z, -1); self.R0(Y, Z, -1); self.L(Z, True)
        self.V(X, Z, -1); self.L(Z); self.J(Y, Z, 1); self.R0(Y, Z, 1); self.L(Z, True)


def scalar_checks(g, S, ncols=None, chunk=1500, seed=1):
    """All basis vectors of (X, Y, Z) (or ncols random ones): forward gives
    Y+X and restores X, Z; inverse gives Y-X."""
    rng = np.random.default_rng(seed)
    v, nr = g.v, S.R.n
    tot = 2 * v + nr
    ok = {'forward': True, 'inverse': True}
    cols_done = 0
    cols = range(tot) if ncols is None else None
    start = 0
    while True:
        if ncols is None:
            if start >= tot:
                break
            idx = np.arange(start, min(tot, start + chunk))
            M = np.zeros((tot, len(idx)), dtype=np.int64)
            M[idx, np.arange(len(idx))] = 1
            start += chunk
        else:
            if cols_done >= ncols:
                break
            M = rng.integers(0, 3, size=(tot, min(chunk, ncols - cols_done)), dtype=np.int64)
        for name, fn, sg in (('forward', S.forward, 1), ('inverse', S.inverse, -1)):
            X, Y, Z = M[:v].copy(), M[v:2 * v].copy(), M[2 * v:].copy()
            fn(X, Y, Z)
            good = (X == M[:v]).all() and (Z == M[2 * v:]).all() and (Y == (M[v:2 * v] + sg * M[:v]) % 3).all()
            ok[name] &= bool(good)
        cols_done += M.shape[1]
    ok['columns'] = cols_done
    return ok


# ------------------------------------------------------------ matching pi
def euler_successor(vertices):
    """Euler circuit of the complete graph on an odd number of vertices
    (Hierholzer, own implementation); returns successor map on edges."""
    adj = {x: set(vertices) - {x} for x in vertices}
    stack, tour = [vertices[0]], []
    while stack:
        x = stack[-1]
        if adj[x]:
            y = max(adj[x])
            adj[x].remove(y); adj[y].remove(x)
            stack.append(y)
        else:
            tour.append(stack.pop())
    edges = [frozenset(e) for e in zip(tour, tour[1:])]
    assert len(set(edges)) == len(edges) == len(vertices) * (len(vertices) - 1) // 2
    for e1, e2 in zip(edges, edges[1:] + edges[:1]):
        assert len(e1 & e2) == 1
    return {e: edges[(i + 1) % len(edges)] for i, e in enumerate(edges)}


def matching(h):
    """pi from the note: pair ground points (2i, 2i+1)."""
    q = h // 2
    succ = {s: euler_successor([j for j in range(q) if j != s]) for s in range(q)}
    five = [m for m in range(1 << h) if bin(m).count('1') == 5]
    pi = {}
    for T in five:
        pts = [p for p in range(h) if T >> p & 1]
        full = sorted({p // 2 for p in pts if T >> (p ^ 1) & 1})
        singles = [p for p in pts if not T >> (p ^ 1) & 1]
        if not full:
            singles.sort(key=lambda p: p // 2)
            keep = singles[:2]
            U = sum(1 << p for p in keep) | sum(1 << (p ^ 1) for p in singles[2:])
        elif len(full) == 1:
            U = sum(1 << p for p in pts if p // 2 == full[0]) | sum(1 << (p ^ 1) for p in singles)
        else:
            (u,) = singles
            new = succ[u // 2][frozenset(full)]
            U = sum((1 << (2 * j)) | (1 << (2 * j + 1)) for j in new) | (1 << (u ^ 1))
        pi[T] = U
    imgs = set(pi.values())
    return pi, dict(h=h, domain=len(five), bijective=len(imgs) == len(five) and imgs <= set(five),
                    meets_two=all(bin(T & U).count('1') == 2 for T, U in pi.items()),
                    classes_preserved=all(
                        len({p // 2 for p in range(h) if T >> p & 1 and T >> (p ^ 1) & 1}) ==
                        len({p // 2 for p in range(h) if U >> p & 1 and U >> (p ^ 1) & 1}) for T, U in pi.items()))


def three_stage(g, S, seed=3):
    """Full exchange on T^3 with dirty scratch, stage-1 bank (A,B) shared with
    the stage-3 bank (B, pi(A)); final negation of X."""
    rng = np.random.default_rng(seed)
    v, nr = g.v, S.R.n
    pi_m, _ = matching(g.h)
    pi = [g.idx[pi_m[m]] for m in g.five]
    X = rng.integers(0, 3, size=(v, v, v)); Y = rng.integers(0, 3, size=(v, v, v))
    X0, Y0 = X.copy(), Y.copy()
    Z1 = rng.integers(0, 3, size=(nr, v, v)); Z2 = rng.integers(0, 3, size=(nr, v, v))
    Z10, Z20 = Z1.copy(), Z2.copy()
    Z3 = np.empty_like(Z1)          # Z3[:, B, pi(A)] is the same bank as Z1[:, A, B]

    def stage(j, fn, src, dst, Z):
        s = np.moveaxis(src, j - 1, 0).reshape(v, v * v)
        d = np.moveaxis(dst, j - 1, 0).reshape(v, v * v)
        Zf = Z.reshape(nr, v * v)
        fn(s, d, Zf)
        return np.moveaxis(s.reshape(v, v, v), 0, j - 1), np.moveaxis(d.reshape(v, v, v), 0, j - 1), Zf.reshape(nr, v, v)
    X, Y, Z1 = stage(1, S.forward, X, Y, Z1)
    Y, X, Z2 = stage(2, S.inverse, Y, X, Z2)
    for A in range(v):
        for B in range(v):
            Z3[:, B, pi[A]] = Z1[:, A, B]
    X, Y, Z3 = stage(3, S.forward, X, Y, Z3)
    back = np.empty_like(Z1)
    for A in range(v):
        for B in range(v):
            back[:, A, B] = Z3[:, B, pi[A]]
    X = (-X) % 3
    return dict(exchange=bool((X == Y0).all() and (Y == X0).all()),
                restored=bool((back == Z10).all() and (Z2 == Z20).all()))


# ----------------------------------------------------- exact rational frames
def rref(vecs):
    rows, piv = [], []
    for v0 in vecs:
        v = list(v0)
        for r, p in zip(rows, piv):
            if v[p]:
                f = v[p]
                v = [x - f * y for x, y in zip(v, r)]
        nz = next((i for i, x in enumerate(v) if x), None)
        if nz is None:
            continue
        f = v[nz]
        v = [x / f for x in v]
        for i, (r, p) in enumerate(zip(rows, piv)):
            if r[nz]:
                g = r[nz]
                rows[i] = [x - g * y for x, y in zip(r, v)]
        rows.append(v)
        piv.append(nz)
    return rows


def form(x, y):
    return sum(a * b for a, b in zip(x, y)) - ALPHA * sum(x) * sum(y)


class Spaces:
    def __init__(self, g, sup, core):
        self.g, self.h = g, g.h
        self.sup = sup
        self.cache = {}
        self.ndg = {}
        self.ucache = {}

    def vec(self, m):
        return [Q(1) if m >> p & 1 else Q(0) for p in range(self.h)]

    def U(self, z):
        b = self.ucache.get(z)
        if b is None:
            g = self.g
            if z < g.v:
                b = rref([self.vec(g.five[z])])
            else:
                a, c = g.adds[z - g.v]
                b = rref(self.U(a) + self.U(c))
            self.ucache[z] = b
        return b

    def perp(self, basis):
        h = self.h
        rows = rref([[u[j] - ALPHA * sum(u) for j in range(h)] for u in basis])
        piv = [next(i for i, x in enumerate(r) if x) for r in rows]
        out = []
        for f in range(h):
            if f in piv:
                continue
            x = [Q(0)] * h
            x[f] = Q(1)
            for r, p in zip(rows, piv):
                x[p] = -r[f]
            out.append(x)
        return rref(out)

    def space(self, key):
        sp = self.cache.get(key)
        if sp is not None:
            return sp
        h, g = self.h, self.g
        k = key[0]
        if k == '0':
            sp = []
        elif k == 'F':
            sp = rref([[Q(int(i == j)) for j in range(h)] for i in range(h)])
        elif k == 'line':
            sp = rref([self.vec(g.five[key[1]])])
        elif k == 'tperp':
            sp = self.perp(rref([self.vec(g.five[key[1]])]))
        elif k == 'U':
            sp = self.U(key[1])
        elif k == 'Up':
            sp = self.perp(self.U(key[1]))
        self.cache[key] = sp
        return sp

    def nondeg(self, key):
        r = self.ndg.get(key)
        if r is None:
            B = self.space(key)
            gram = [[form(x, y) for y in B] for x in B]
            r = len(rref(gram)) == len(B)
            self.ndg[key] = r
        return r


class EdgeCheck:
    def __init__(self, sp):
        self.sp = sp
        self.cache = {}

    def part(self, k1, k2):
        """(sign, |dim change|, ok, why) for label k1 -> k2 in F."""
        key = (k1, k2)
        r = self.cache.get(key)
        if r is not None:
            return r
        sp = self.sp
        if not sp.nondeg(k1) or not sp.nondeg(k2):
            r = (0, 0, False, 'degenerate label')
        else:
            A, B = sp.space(k1), sp.space(k2)
            d1, d2 = len(A), len(B)
            du = len(rref(A + B))
            if du == max(d1, d2):
                if d1 == d2:
                    r = (0, 0, True, '')
                else:
                    r = (1 if d2 > d1 else -1, abs(d2 - d1), True, '')
            else:
                r = (0, 0, False, 'incomparable')
        self.cache[key] = r
        return r


D0 = ('F', '0')
D1 = ('F', 'F')


def schedule(g, R, kinds, stage2):
    """Gate list (tag, wires, (Bkey, Pkey)). Wires: ('X',t), ('Y',t), ('r',role)."""
    v = g.v
    inj = [[] for _ in range(v)]
    ret = []
    for o, k in enumerate(kinds):
        if k[0] == 'D':
            inj[g.idx[k[2]]].append(R.out[o])
        else:
            ret.append((R.out[o], k[1]))
    gates = []

    def Lg(frame_of, inv=False):
        for z, p, s, fan in (reversed(R.gates) if inv else R.gates):
            gates.append(('L', [('r', p), ('r', s)] + [('r', f) for f in fan], frame_of(z)))

    def Jg(bank, frame_of):
        for t in range(v):
            gates.append(('J', [(bank, t)] + [('r', r) for r in inj[t]], frame_of(t)))

    def R0g(bank, frame):
        gates.append(('R0', [(bank, t) for t in range(v)] + [('r', r) for r, C in ret], frame))

    def Vg(bank, frame_of):
        for t in range(v):
            gates.append(('V', [(bank, t)] + [('r', r) for r in R.slots[t]], frame_of(t)))
    U = lambda z: ('F', ('U', z))
    Up = lambda z: ('F', ('Up', z))
    Xt = lambda t: ('F', ('line', t))
    Yt = lambda t: ('F', ('tperp', t))
    if not stage2:
        Lg(lambda z: D0); R0g('Y', D0); Jg('Y', lambda t: D0); Lg(lambda z: D0, True)
        if MUTANT == 'J_before_R0':
            Vg('X', Xt); Lg(U); Jg('Y', Yt); R0g('Y', D0); Lg(lambda z: D1, True); Vg('X', lambda t: D1)
        else:
            Vg('X', Xt); Lg(U); R0g('Y', D0); Jg('Y', Yt); Lg(lambda z: D1, True); Vg('X', lambda t: D1)
    else:
        Vg('Y', lambda t: D0); Lg(lambda z: D0); Jg('X', Xt); R0g('X', D1); Lg(U if MUTANT == 'stage2_uncomplemented' else Up, True)
        Vg('Y', Yt); Lg(lambda z: D1); Jg('X', lambda t: D1); R0g('X', D1); Lg(lambda z: D1, True)
    return gates


def frames_check(g, R, kinds, sp, stage, stage2):
    h, v = g.h, g.v
    m = h ** 3
    a = h ** (stage - 1)
    ec = EdgeCheck(sp)
    seq = {}
    for tag, wires, fr in schedule(g, R, kinds, stage2):
        for w in wires:
            seq.setdefault(w, []).append((fr, tag))
    fails, dec, tot = [], [], 0
    for w, frs in seq.items():
        if w[0] == 'X':
            chain = [(('line', w[1]), ('line', w[1]))] + [f for f, _ in frs] + [D1]
        elif w[0] == 'Y':
            chain = [(('line', w[1]), '0')] + [f for f, _ in frs] + [('F', ('tperp', w[1]))]
        else:
            chain = [('0', '0')] + [f for f, _ in frs]
            if chain[-1] != D1:
                fails.append((w, 'aux last frame not D_1', chain[-1]))
            tot += m - h * a
        tags = ['src'] + [t for _, t in frs] + ['snk']
        for i in range(len(chain) - 1):
            (b1, p1), (b2, p2) = chain[i], chain[i + 1]
            sb, db, okb, wb = ec.part(b1, b2) if a > 1 else (0, 0, True, '')
            spp, dp, okp, wp = ec.part(p1, p2)
            if not (okb and okp) or sb * spp < 0:
                fails.append((w, i, chain[i], chain[i + 1], wb or wp or 'opposite'))
                continue
            ch = (a - 1) * db + dp
            tot += ch
            if (sb or spp) < 0:
                dec.append((w, tags[i], tags[i + 1], ch))
    nret = sum(1 for k in kinds if k[0] == 'A')
    loss = sum(d[3] for d in dec)
    dec_ret = all(d[0][0] == 'r' and d[3] == h - 2 for d in dec)
    want = R.n * m + 2 * loss + 2 * v * a * (h - 1)
    return dict(stage=stage, reverse=stage2, fails=len(fails), first=fails[:3], decreases=len(dec),
                retained=nret, only_retained_lose_h_minus_2=dec_ret and len(dec) == nret,
                loss=loss, loss_expected=nret * (h - 2), sum_abs=tot, sum_abs_expected=want,
                ok=not fails and dec_ret and len(dec) == nret and tot == want)


def run(g, label, frames=True, basis=True, three=False):
    t0 = time.time()
    sup, core, kinds, fails = check_structure(g)
    R = Roles(g)
    rep = dict(producer=label, h=g.h, v=g.v, c=len(g.adds), q=len(g.outputs), roles=R.n,
               roles_eq_c_plus_q=R.n == len(g.adds) + len(g.outputs), structure_fails=fails[:5])
    ok = not fails and rep['roles_eq_c_plus_q']
    if not fails:
        S = Scalar(g, R, kinds)
        sc = scalar_checks(g, S, ncols=None if basis else 64)
        rep['scalar'] = sc
        ok &= sc['forward'] and sc['inverse']
        if three:
            rep['three_stage'] = three_stage(g, S)
            ok &= all(rep['three_stage'].values())
        if frames:
            sp = Spaces(g, sup, core)
            # exact positive definiteness of every node label (stronger than nondegenerate)
            rep['frames'] = []
            for st, rev in ((1, False), (2, True), (3, False)):
                f = frames_check(g, R, kinds, sp, st, rev)
                rep['frames'].append(f)
                ok &= f['ok']
            dims = {len(sp.U(z)) for z, k in zip([o[0] for o in g.outputs], kinds) if k[0] == 'A'}
            rep['retained_span_dims'] = sorted(dims)
            ok &= dims == {g.h - 2}
    rep['PASS'] = bool(ok)
    rep['seconds'] = round(time.time() - t0, 1)
    return rep


if __name__ == '__main__':
    args = sys.argv[1:]
    h = int(args[0])
    which = args[1]
    if which == 'mine':
        g = mine(h)
    elif which == 'final':
        g = load_final(args[2], h)
    print(json.dumps(run(g, which, frames='--noframes' not in args, basis='--random' not in args,
                         three='--three' in args)), flush=True)
