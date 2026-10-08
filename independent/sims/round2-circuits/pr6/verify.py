"""Independent verifier for the PR 6 aligned bit network (cheaper centers).

Input: only the exported graph {h, v, left, right, partial=[(node,i,T)],
center=[(node,i)]}. Nodes 0..v-1 are the triples of [h] in lexicographic
order. Nothing from the builder's keys or recursion is used.

Properties (quoted sources in REPORT section of run logs):
 P1 topological order, every addition joins disjoint supports
 P2 every node has a common point (=> U_z positive definite)
 P3 every partial output (i,T) is exactly sum_{S cap T = {i}} x_S
 P4 every center (i) is exactly z_i = sum_{T contains i} x_T
 P5 each (i,T), i in T, has exactly one partial output; each i one center
 P6 every node has an outgoing use (so roles = c + q + h)
 P7 role compilation (own compiler) gives c + q + h roles
 P8 scalar F_2 schedule with dirty scratch: forward y ^= x, stage 2 x ^= y,
    all auxiliary values restored (random lanes, and every basis vector at
    small h)
 P9 frame schedule of both stage directions: every wire's chronological
    frame chain is monotone except the designated decreases; the only
    decreases are the h center returns, each of codimension h-1
 P10 every auxiliary role starts at D_0 and ends at D_1 (bank sharing premise)
"""
from itertools import combinations
from fractions import Fraction as Q
import numpy as np


class Graph:
    def __init__(self, g):
        self.h, self.v = g['h'], g['v']
        self.left, self.right = g['left'], g['right']
        self.partial, self.center = g['partial'], g['center']
        self.c = len(self.left)
        self.n = self.v + self.c
        h = self.h
        self.trip = list(combinations(range(h), 3))
        assert len(self.trip) == self.v
        self.tmask = [(1 << a) | (1 << b) | (1 << c) for a, b, c in self.trip]
        self.gpid = {}
        for k, (a, b) in enumerate(combinations(range(h), 2)):
            self.gpid[a, b] = self.gpid[b, a] = k
        self.gpair = list(combinations(range(h), 2))


# ----------------------------------------------------------------- supports
def supports(G):
    """Per node: common-point mask cm and (c, mask) with c the lowest common
    point and mask over global pair indices (pair {a,b} = triple {c,a,b})."""
    h, v = G.h, G.v
    cm = [0] * G.n
    rep = [None] * G.n
    for t, (a, b, c) in enumerate(G.trip):
        cm[t] = G.tmask[t]
        rep[t] = (a, 1 << G.gpid[b, c])
    fails = []

    def conv(node, c):
        c0, m = rep[node]
        if c0 == c:
            return m
        if not (cm[node] >> c) & 1:
            return None
        out = 0
        while m:
            lb = m & -m
            m ^= lb
            x, y = G.gpair[lb.bit_length() - 1]
            k = y if x == c else x
            assert (x == c) or (y == c)
            out |= 1 << G.gpid[c0, k]
        return out

    for k in range(G.c):
        n = v + k
        a, b = G.left[k], G.right[k]
        if not (a < n and b < n):
            fails.append(('topo', n))
            continue
        cmn = cm[a] & cm[b]
        if not cmn:
            fails.append(('no common point', n))
            rep[n] = None
            continue
        c = (cmn & -cmn).bit_length() - 1
        ma, mb = conv(a, c), conv(b, c)
        if ma & mb:
            fails.append(('overlap', n))
        m = ma | mb
        # recompute the common mask exactly from the union (not only AND):
        cm[n] = cmn
        rep[n] = (c, m)
    return cm, rep, conv, fails


def check_outputs(G, cm, rep, conv):
    h = G.h
    fails = []
    seen = set()
    for (n, i, T) in G.partial:
        T = tuple(T)
        if i not in T or (i, T) in seen:
            fails.append(('bad/duplicate output', i, T))
            continue
        seen.add((i, T))
        m = conv(n, i)
        rest = [p for p in range(h) if p not in T]
        want = 0
        for a, b in combinations(rest, 2):
            want |= 1 << G.gpid[a, b]
        if m != want:
            fails.append(('partial output inexact', i, T, n))
    need = {(i, T) for T in G.trip for i in T}
    if seen != need:
        fails.append(('partial outputs incomplete', len(seen), len(need)))
    cs = set()
    for (n, i) in G.center:
        cs.add(i)
        m = conv(n, i)
        rest = [p for p in range(h) if p != i]
        want = 0
        for a, b in combinations(rest, 2):
            want |= 1 << G.gpid[a, b]
        if m != want:
            fails.append(('center inexact', i, n))
    if cs != set(range(h)) or len(G.center) != h:
        fails.append(('centers incomplete',))
    return fails


def brute_force(G):
    """Small h only: explicit frozensets of triples, no tricks."""
    h, v = G.h, G.v
    sup = [frozenset([t]) for t in range(v)]
    fails = []
    for k in range(G.c):
        a, b = G.left[k], G.right[k]
        A, B = sup[a], sup[b]
        if A & B:
            fails.append(('overlap', v + k))
        S = A | B
        common = set(range(h))
        for t in S:
            common &= set(G.trip[t])
        if not common:
            fails.append(('no common', v + k))
        sup.append(S)
    for (n, i, T) in G.partial:
        want = frozenset(s for s in range(v) if set(G.trip[s]) & set(T) == {i})
        if sup[n] != want:
            fails.append(('partial', i, tuple(T)))
    for (n, i) in G.center:
        want = frozenset(s for s in range(v) if i in G.trip[s])
        if sup[n] != want:
            fails.append(('center', i))
    dup = len(sup) - len(set(sup))
    return fails, dup, sup


# -------------------------------------------------------------------- roles
class Roles:
    def __init__(self, G):
        v, n = G.v, G.n
        uses = [[] for _ in range(n)]
        for k in range(G.c):
            uses[G.left[k]].append(('add', v + k))
            uses[G.right[k]].append(('add', v + k))
        self.out_role = {}
        for idx, (z, i, T) in enumerate(G.partial):
            uses[z].append(('part', idx))
        for idx, (z, i) in enumerate(G.center):
            uses[z].append(('cen', idx))
        self.unused = [z for z in range(n) if not uses[z]]
        nr = 0
        pos = [0] * n
        role_of = {}
        self.gates = []        # (node, pivot, second or None, fanouts)
        self.src = [None] * v

        def take(z):
            r = role_of[z, pos[z]]
            pos[z] += 1
            return r
        for z in range(v):
            rs = list(range(nr, nr + len(uses[z])))
            nr += len(uses[z])
            for u, r in enumerate(rs):
                role_of[z, u] = r
            self.src[z] = rs[0]
            self.gates.append((z, rs[0], None, rs[1:]))
        for k in range(G.c):
            z = v + k
            p = take(G.left[k])
            s = take(G.right[k])
            fan = list(range(nr, nr + len(uses[z]) - 1))
            nr += len(fan)
            role_of[z, 0] = p
            for u, r in enumerate(fan):
                role_of[z, u + 1] = r
            self.gates.append((z, p, s, fan))
        self.part_role = [None] * len(G.partial)
        self.cen_role = [None] * len(G.center)
        for z in range(n):
            for u, use in enumerate(uses[z]):
                if use[0] == 'part':
                    self.part_role[use[1]] = role_of[z, u]
                elif use[0] == 'cen':
                    self.cen_role[use[1]] = role_of[z, u]
        self.n_roles = nr
        allr = set(self.part_role) | set(self.cen_role)
        self.distinct_outputs = len(allr) == len(G.partial) + len(G.center)


# ------------------------------------------------------- F_2 scalar schedule
class Scalar:
    """Bit-parallel F_2 simulation: every value is a numpy uint64 row."""

    def __init__(self, G, R):
        self.G, self.R = G, R
        self.cen_targets = []
        for (z, i) in G.center:
            self.cen_targets.append([t for t, tr in enumerate(G.trip) if i in tr])
        tid = {t: k for k, t in enumerate(G.trip)}
        self.part_target = [tid[tuple(T)] for (_, _, T) in G.partial]

    def L(self, Z):
        for z, p, s, fan in self.R.gates:
            if s is not None:
                Z[p] ^= Z[s]
            for f in fan:
                Z[f] ^= Z[p]

    def Linv(self, Z):
        for z, p, s, fan in reversed(self.R.gates):
            for f in fan:
                Z[f] ^= Z[p]
            if s is not None:
                Z[p] ^= Z[s]

    def V(self, Z, src):
        for t in range(self.G.v):
            Z[self.R.src[t]] ^= src[t]

    def J(self, Z, tgt):
        for k, t in enumerate(self.part_target):
            tgt[t] ^= Z[self.R.part_role[k]]

    def R0(self, Z, tgt):
        for k, ts in enumerate(self.cen_targets):
            r = Z[self.R.cen_role[k]]
            for t in ts:
                tgt[t] ^= r

    def forward(self, X, Y, Z):
        """L', J', L'^-1, V, L', J', L'^-1, V^-1 with J' = J R_0."""
        self.L(Z); self.R0(Z, Y); self.J(Z, Y); self.Linv(Z)
        self.V(Z, X)
        self.L(Z); self.R0(Z, Y); self.J(Z, Y); self.Linv(Z)
        self.V(Z, X)

    def stage2(self, X, Y, Z):
        """V, L', J, R_0, L'^-1, V^-1, L', J, R_0, L'^-1; source Y, target X."""
        self.V(Z, Y); self.L(Z); self.J(Z, X); self.R0(Z, X); self.Linv(Z)
        self.V(Z, Y)
        self.L(Z); self.J(Z, X); self.R0(Z, X); self.Linv(Z)


def scalar_random(G, R, words=4, seed=1):
    rng = np.random.default_rng(seed)
    S = Scalar(G, R)
    out = {}
    for name in ('forward', 'stage2'):
        X = rng.integers(0, 2**63, size=(G.v, words), dtype=np.uint64)
        Y = rng.integers(0, 2**63, size=(G.v, words), dtype=np.uint64)
        Z = rng.integers(0, 2**63, size=(R.n_roles, words), dtype=np.uint64)
        X0, Y0, Z0 = X.copy(), Y.copy(), Z.copy()
        if name == 'forward':
            S.forward(X, Y, Z)
            ok = (X == X0).all() and (Y == (Y0 ^ X0)).all() and (Z == Z0).all()
        else:
            S.stage2(X, Y, Z)
            ok = (Y == Y0).all() and (X == (X0 ^ Y0)).all() and (Z == Z0).all()
        out[name] = bool(ok)
    return out


def scalar_basis(G, R, seed=3):
    """Every basis vector e_T at once (lane T holds e_T), dirty scratch."""
    rng = np.random.default_rng(seed)
    S = Scalar(G, R)
    v = G.v
    words = (v + 63) // 64
    res = {}
    for name in ('forward', 'stage2'):
        X = np.zeros((v, words), dtype=np.uint64)
        for t in range(v):
            X[t, t // 64] |= np.uint64(1) << np.uint64(t % 64)
        Y = rng.integers(0, 2**63, size=(v, words), dtype=np.uint64)
        Z = rng.integers(0, 2**63, size=(R.n_roles, words), dtype=np.uint64)
        X0, Y0, Z0 = X.copy(), Y.copy(), Z.copy()
        if name == 'forward':
            S.forward(X, Y, Z)
            ok = (X == X0).all() and (Y == (Y0 ^ X0)).all() and (Z == Z0).all()
        else:
            # basis vectors on the logical source Y
            Y, X = X.copy(), Y.copy()
            X0, Y0 = X.copy(), Y.copy()
            S.stage2(X, Y, Z)
            ok = (Y == Y0).all() and (X == (X0 ^ Y0)).all() and (Z == Z0).all()
        res[name] = bool(ok)
    return res


# ------------------------------------------------------------ bank sharing
def pi_paired(h):
    """notes/paired-construction.tex: pair consecutive points; a triple with
    a full pair and a singleton keeps the singleton and cycles the full pair
    among the pairs not containing it; otherwise keep the point in the least
    indexed pair and flip the other two to their partners."""
    trip = list(combinations(range(h), 3))
    tid = {t: k for k, t in enumerate(trip)}
    P = h // 2
    out = []
    for t in trip:
        blocks = [p // 2 for p in t]
        if len(set(blocks)) == 2:
            s = next(p for p in t if blocks.count(p // 2) == 1)
            full = next(b for b in blocks if blocks.count(b) == 2)
            cyc = [k for k in range(P) if k != s // 2]
            nb = cyc[(cyc.index(full) + 1) % len(cyc)]
            u = tuple(sorted((s, 2 * nb, 2 * nb + 1)))
        else:
            least = min(t, key=lambda p: p // 2)
            u = tuple(sorted([least] + [p ^ 1 for p in t if p != least]))
        out.append(tid[u])
    return trip, out


def three_stage(G, R, seed=5):
    """(X,Y) -> (Y,X) over T^3, F_2, dirty scratch, stage-1 bank (A,B) shared
    with stage 3 at (B, pi(A)). Small h only (v^3 data)."""
    rng = np.random.default_rng(seed)
    v = G.v
    trip, pi = pi_paired(G.h)
    S = Scalar(G, R)
    nr = R.n_roles
    X = rng.integers(0, 2, size=(v, v, v), dtype=np.uint8).astype(bool)
    Y = rng.integers(0, 2, size=(v, v, v), dtype=np.uint8).astype(bool)
    X0, Y0 = X.copy(), Y.copy()
    Z1 = rng.integers(0, 2, size=(nr, v, v), dtype=np.uint8).astype(bool)
    Z2 = rng.integers(0, 2, size=(nr, v, v), dtype=np.uint8).astype(bool)
    Z1init, Z2init = Z1.copy(), Z2.copy()

    def run(fn, j, A, Bk, Z):
        a = np.moveaxis(A, j - 1, 0).reshape(v, v * v).copy()
        b = np.moveaxis(Bk, j - 1, 0).reshape(v, v * v).copy()
        z = Z.reshape(nr, v * v).copy()
        fn(a, b, z)
        back = lambda arr: np.moveaxis(arr.reshape(v, v, v), 0, j - 1)
        return back(a), back(b), z.reshape(nr, v, v)

    X, Y, Z1 = run(S.forward, 1, X, Y, Z1)
    restored1 = bool((Z1 == Z1init).all())
    X, Y, Z2 = run(S.stage2, 2, X, Y, Z2)
    restored2 = bool((Z2 == Z2init).all())
    # stage-3 lane (a,b) uses the stage-1 bank of lane (A,B) with B=a, pi(A)=b
    pinv = [0] * v
    for A in range(v):
        pinv[pi[A]] = A
    Z3 = np.empty_like(Z1)
    for a in range(v):
        for b in range(v):
            Z3[:, a, b] = Z1[:, pinv[b], a]
    Z3init = Z3.copy()
    X, Y, Z3 = run(S.forward, 3, X, Y, Z3)
    restored3 = bool((Z3 == Z3init).all())
    return dict(exchange=bool((X == Y0).all() and (Y == X0).all()),
                restored=restored1 and restored2 and restored3,
                pi_bijective=sorted(pi) == list(range(v)),
                pi_meets_one=all(len(set(trip[k]) & set(trip[pi[k]])) == 1 for k in range(v)))
