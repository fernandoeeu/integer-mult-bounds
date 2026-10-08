"""Independent implementation of PR 3's compressed complex side circuit,
written from notes/complex-circuit-construction.tex only.

Generic in h.  At the top level L = first floor(h/2) points, R = the rest,
exactly as the note's L={0..11}, R={12..24} at h=25.
"""
from fractions import Fraction
from itertools import combinations
from circuit import Circuit

HALF = Fraction(1, 2)


def subsets_upto(pts, k):
    out = []
    for r in range(0, min(k, len(pts)) + 1):
        out.extend(frozenset(c) for c in combinations(pts, r))
    return out


class PR3Builder:
    def __init__(self, h, add_order='lr'):
        self.h = h
        C = self.C = Circuit(h)
        self.dsupp = {}   # disjoint family: triple-bitmask -> node
        self.nsupp = {}   # node -> triple-bitmask (both families)
        for i in range(C.v):
            self.nsupp[i] = 1 << i
        self.pts_of = {}  # node -> point mask covered (disjoint family)
        for i, t in enumerate(C.T):
            self.pts_of[i] = t

    # ---------------- disjoint family ------------------------------
    def dadd(self, a, b):
        if a is None:
            return b
        if b is None:
            return a
        sa, sb = self.nsupp[a], self.nsupp[b]
        assert sa & sb == 0, "summands must have disjoint supports"
        s = sa | sb
        z = self.dsupp.get(s)
        if z is None:
            X = self.pts_of[a] | self.pts_of[b]
            z = self.C.add(a, b, 'disj', ('coord', X))
            self.dsupp[s] = z
            self.nsupp[z] = s
            self.pts_of[z] = X
        return z

    def vec(self, items, k):
        """items: list of (point, node or None), distinct points, sorted.
        Returns {E: node} for every E subset of the points, |E|<=k: the sum
        of the nodes whose point avoids E."""
        n = len(items)
        if n == 0:
            return {frozenset(): None}
        if n == 1:
            p, z = items[0]
            out = {frozenset(): z}
            if k >= 1:
                out[frozenset([p])] = None
            return out
        Lh, Rh = items[:n // 2], items[n // 2:]
        Lo, Ro = self.vec(Lh, k), self.vec(Rh, k)
        Lp = [p for p, _ in Lh]
        Rp = [p for p, _ in Rh]
        out = {}
        for E in subsets_upto([p for p, _ in items], k):
            EL = E & frozenset(Lp)
            ER = E & frozenset(Rp)
            out[E] = self.dadd(Lo[EL], Ro[ER])
        return out

    def pairs(self, X, w, k=3):
        """X sorted point list; w(u,v) -> node.  {E: sum over pairs avoiding E}."""
        n = len(X)
        if n < 2:
            return {E: None for E in subsets_upto(X, k)}
        L, R = X[:n // 2], X[n // 2:]
        PL, PR = self.pairs(L, w, k), self.pairs(R, w, k)
        rows = {u: self.vec([(r, w(u, r)) for r in R], k) for u in L}
        cols = {}
        for ER in subsets_upto(R, k):
            cols[ER] = self.vec([(u, rows[u][ER]) for u in L], k - len(ER))
        out = {}
        for E in subsets_upto(X, k):
            EL = E & frozenset(L)
            ER = E & frozenset(R)
            out[E] = self.dadd(self.dadd(PL[EL], PR[ER]), cols[ER][EL])
        return out

    def tri_parts(self, X, k=3):
        n = len(X)
        L, R = X[:n // 2], X[n // 2:]
        T = self.C.tidx
        P = {r: self.pairs(L, lambda u, v, r=r: T[(1 << u) | (1 << v) | (1 << r)], k) for r in R}
        Pp = {u: self.pairs(R, lambda a, b, u=u: T[(1 << u) | (1 << a) | (1 << b)], k) for u in L}
        return L, R, P, Pp

    def tri(self, X, k=3):
        n = len(X)
        if n < 3:
            return {E: None for E in subsets_upto(X, k)}
        L, R, P, Pp = self.tri_parts(X, k)
        TL, TR = self.tri(L, k), self.tri(R, k)
        V1 = {EL: self.vec([(r, P[r][EL]) for r in R], k - len(EL)) for EL in subsets_upto(L, k)}
        V2 = {ER: self.vec([(u, Pp[u][ER]) for u in L], k - len(ER)) for ER in subsets_upto(R, k)}
        out = {}
        for E in subsets_upto(X, k):
            EL = E & frozenset(L)
            ER = E & frozenset(R)
            if len(EL) > k or len(ER) > k:
                continue
            s = self.dadd(TL[EL], TR[ER])
            s = self.dadd(s, V1[EL][ER])
            s = self.dadd(s, V2[ER][EL])
            out[E] = s
        return out

    # ---------------- pair stars -----------------------------------
    def stars(self):
        h, C, T = self.h, self.C, self.C.tidx
        self.star = {}
        for a, b in combinations(range(h), 2):
            ab = (1 << a) | (1 << b)
            us = [u for u in range(h) if u not in (a, b)]
            n = len(us)
            leaf = [T[ab | (1 << u)] for u in us]
            pre = [None] * (n + 2)   # pre[i] = pi_i (1-based), pre[0]=None
            suf = [None] * (n + 2)   # suf[i] = sigma_i, suf[n+1]=None
            # nodes are created lazily below; keep descriptors
            self.star[(a, b)] = (us, leaf)

    def star_prefix(self, a, b, i):
        """pi_i over the first i leaves (1-based), built as a chain."""
        us, leaf = self.star[(a, b)]
        key = ('pre', a, b, i)
        if key in self.memo:
            return self.memo[key]
        if i == 0:
            z = None
        elif i == 1:
            z = leaf[0]
        else:
            prev = self.star_prefix(a, b, i - 1)
            lam = 0
            for u in us[:i]:
                lam |= 1 << u
            z = self.C.add(prev, leaf[i - 1], 'star', ('star', (1 << a) | (1 << b), lam))
            self.nsupp[z] = self.nsupp[prev] | self.nsupp[leaf[i - 1]]
        self.memo[key] = z
        return z

    def star_suffix(self, a, b, i):
        us, leaf = self.star[(a, b)]
        n = len(us)
        key = ('suf', a, b, i)
        if key in self.memo:
            return self.memo[key]
        if i == n + 1:
            z = None
        elif i == n:
            z = leaf[n - 1]
        else:
            nxt = self.star_suffix(a, b, i + 1)
            lam = 0
            for u in us[i - 1:]:
                lam |= 1 << u
            z = self.C.add(nxt, leaf[i - 1], 'star', ('star', (1 << a) | (1 << b), lam))
            self.nsupp[z] = self.nsupp[nxt] | self.nsupp[leaf[i - 1]]
        self.memo[key] = z
        return z

    # ---------------- assembly --------------------------------------
    def covered_points(self, z):
        s = self.nsupp[z]
        X = 0
        T = self.C.T
        while s:
            b = s.bit_length() - 1
            X |= T[b]
            s ^= 1 << b
        return X

    def inject(self, z, S, coeff, log):
        """Injection rule: split pieces that cover every point outside S."""
        if z is None:
            return
        full = ((1 << self.h) - 1) & ~S
        if self.covered_points(z) & full == full:
            log.append((self.C.family[z], z, S))
            assert self.C.kind[z] == 'add', "single triple cannot cover everything"
            a, b = self.C.args[z]
            self.inject(a, S, coeff, log)
            self.inject(b, S, coeff, log)
            return
        self.C.outputs.append((z, self.C.tidx[S], coeff))

    def build(self):
        h, C = self.h, self.C
        self.memo = {}
        pts = list(range(h))
        L, R = pts[:h // 2], pts[h // 2:]
        TL = self.tri(L)
        TR = self.tri(R)
        _, _, P, Pp = None, None, None, None
        T = C.tidx
        P = {r: self.pairs(L, lambda u, v, r=r: T[(1 << u) | (1 << v) | (1 << r)]) for r in R}
        Pp = {u: self.pairs(R, lambda a, b, u=u: T[(1 << u) | (1 << a) | (1 << b)]) for u in L}
        R1, R2 = R[:len(R) // 2], R[len(R) // 2:]
        L1, L2 = L[:len(L) // 2], L[len(L) // 2:]
        self.stars()
        self.split_log = []
        pieces_per_target = {}
        for Smask in C.T:
            S = [p for p in range(h) if Smask >> p & 1]
            SL = frozenset(p for p in S if p in L)
            SR = frozenset(p for p in S if p in R)
            pieces = [TL[SL], TR[SR]]
            for half in (R1, R2):
                d = self.vec([(r, P[r][SL]) for r in half], 3 - len(SL))
                pieces.append(d[SR & frozenset(half)])
            for half in (L1, L2):
                d = self.vec([(u, Pp[u][SR]) for u in half], 3 - len(SR))
                pieces.append(d[SL & frozenset(half)])
            before = len(C.outputs)
            for z in pieces:
                self.inject(z, Smask, HALF, self.split_log)
            # pair stars
            for a, b in combinations(S, 2):
                us, leaf = self.star[(a, b)]
                (u,) = [p for p in S if p not in (a, b)]
                i = us.index(u) + 1
                self.inject(self.star_prefix(a, b, i - 1), Smask, -HALF, self.split_log)
                self.inject(self.star_suffix(a, b, i + 1), Smask, -HALF, self.split_log)
            pieces_per_target[Smask] = len(C.outputs) - before
        self.pieces_per_target = pieces_per_target
        C.prune()
        return C


def build(h):
    B = PR3Builder(h)
    C = B.build()
    C.split_log = B.split_log
    C.pieces_per_target = B.pieces_per_target
    return C


def label_space(C, key, Space):
    """Binary label in F_2^h for a label key."""
    h = C.h
    kind = key[0]
    if kind == 'line':
        return Space(h, [C.T[key[1]]])
    if kind == 'coord':
        X = key[1]
        return Space(h, [1 << p for p in range(h) if X >> p & 1])
    if kind == 'star':
        ab, lam = key[1], key[2]
        return Space(h, [ab | (1 << u) for u in range(h) if lam >> u & 1])
    raise ValueError(key)
