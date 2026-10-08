"""Independent implementation of PR 4's retained-total complex motif,
written from notes/retained-complex-construction.tex only.

Design choices where the note is not explicit (documented in REPORT.md):
 * rectangle partition: recursive row-star / column-star / half-split with
   products, choosing at every subproblem the option of least role cost
   sum(a+b-1) with the children chosen the same way (the note's selection
   rule is not written down);
 * balanced trees split at floor(n/2); global tree: balanced trees over
   the third point within (least, second) groups, then over second points,
   then over least points.
"""
from fractions import Fraction
from itertools import combinations
from functools import lru_cache
from math import comb
from circuit import Circuit

HALF = Fraction(1, 2)
QUARTER = Fraction(1, 4)


def ksubsets(mask, k):
    pts = [p for p in range(mask.bit_length()) if mask >> p & 1]
    return [sum(1 << p for p in c) for c in combinations(pts, k)]


class RectPlanner:
    """Exact rectangle partitions of {(s,t): |s|=a, |t|=b, s,t subset G,
    s & t = 0} by row stars, column stars, or a split of the (ordered) ground
    set into a prefix and a suffix with the product of the smaller partitions
    for every source/target cardinality case.  At each (n,a,b) the option of
    least role cost sum(|A|+|B|-1) is kept (children chosen the same way).
    Summaries (rectangles K, sum|A|, sum|B|) make the product cost exact:
    a product of partitions has K1K2 rectangles, sum|A| = SA1*SA2, etc."""

    def __init__(self, splits='all'):
        self.splits = splits
        self.memo = {}

    def summary(self, n, a, b):
        key = (n, a, b)
        if key in self.memo:
            return self.memo[key]
        if a < 0 or b < 0 or a + b > n:
            r = (0, 0, 0, ('empty',))
        elif a == 0 or b == 0:
            r = (1, comb(n, a), comb(n, b), ('one',))
        else:
            rows = (comb(n, a), comb(n, a), comb(n, a) * comb(n - a, b), ('rows',))
            cols = (comb(n, b), comb(n, b) * comb(n - b, a), comb(n, b), ('cols',))
            best = min((rows, cols), key=lambda x: x[1] + x[2] - x[0])
            ks = range(1, n) if self.splits == 'all' else [n // 2]
            for k in ks:
                K = SA = SB = 0
                terms = []
                for i in range(a + 1):
                    for j in range(b + 1):
                        l = self.summary(k, i, j)
                        r_ = self.summary(n - k, a - i, b - j)
                        if l[0] and r_[0]:
                            K += l[0] * r_[0]
                            SA += l[1] * r_[1]
                            SB += l[2] * r_[2]
                            terms.append(((k, i, j), (n - k, a - i, b - j)))
                cand = (K, SA, SB, ('split', k, tuple(terms)))
                if SA + SB - K < best[1] + best[2] - best[0]:
                    best = cand
            r = best
        self.memo[key] = r
        return r

    def rectangles(self, pts, a, b):
        n = len(pts)
        K, SA, SB, how = self.summary(n, a, b)
        if how[0] == 'empty':
            return []
        S = [sum(1 << pts[x] for x in c) for c in combinations(range(n), a)]
        T = [sum(1 << pts[x] for x in c) for c in combinations(range(n), b)]
        if how[0] == 'one':
            return [(S, T)]
        if how[0] == 'rows':
            return [([s], [t for t in T if not s & t]) for s in S]
        if how[0] == 'cols':
            return [([s for s in S if not s & t], [t]) for t in T]
        k = how[1]
        out = []
        for (n1, i, j), (n2, i2, j2) in how[2]:
            for A1, B1 in self.rectangles(pts[:k], i, j):
                for A2, B2 in self.rectangles(pts[k:], i2, j2):
                    out.append(([x | y for x in A1 for y in A2], [x | y for x in B1 for y in B2]))
        return out

    def plan(self, G, a, b):
        pts = [p for p in range(G.bit_length()) if G >> p & 1]
        return self.rectangles(pts, a, b)


def plan_disjoint(h, splits='all'):
    return RectPlanner(splits).plan((1 << h) - 1, 3, 3)


def balanced(C, leaves, mk_label, family):
    """Balanced binary tree (split at floor(n/2)); returns (root, nodes) where
    nodes maps node -> set of leaf positions (for subtree selection)."""
    info = {}

    def rec(lo, hi):
        if hi - lo == 1:
            z = leaves[lo]
            info[z] = (lo, hi, None, None)
            return z
        mid = lo + (hi - lo) // 2
        a = rec(lo, mid)
        b = rec(mid, hi)
        z = C.add(a, b, family, mk_label(lo, hi))
        info[z] = (lo, hi, a, b)
        return z
    return rec(0, len(leaves)), info


def build(h, plan=None):
    assert h % 2 == 0, "PR 4 needs even h (w_i orthonormality, matching)"
    C = Circuit(h)
    T, tidx = C.T, C.tidx
    full = (1 << h) - 1
    if plan is None:
        plan = plan_disjoint(h)
    C.plan_rectangles = len(plan)
    repaired = 0
    # ----- disjoint branch: rectangles ---------------------------------
    rect_adds = 0
    rect_outs = 0
    for A, B in plan:
        srcs = sorted(tidx[s] for s in A)
        K = 0
        for s in A:
            K |= s
        if len(srcs) > 1 and any((K | t) == full for t in B):
            repaired += 1
            for s in A:
                for t in B:
                    C.outputs.append((tidx[s], tidx[t], HALF))
                    rect_outs += 1
            continue
        if len(srcs) == 1:
            root = srcs[0]
        else:
            def lab(lo, hi, srcs=srcs):
                X = 0
                for q in srcs[lo:hi]:
                    X |= T[q]
                return ('coord', X)
            n0 = C.n_nodes()
            root, _ = balanced(C, srcs, lab, 'rect')
            rect_adds += C.n_nodes() - n0
        for t in B:
            C.outputs.append((root, tidx[t], HALF))
            rect_outs += 1
    C.rect_adds, C.rect_outs, C.repaired = rect_adds, rect_outs, repaired
    # ----- global tree --------------------------------------------------
    n0 = C.n_nodes()
    lvl1 = []
    for i in range(h):
        lvl2 = []
        for j in range(i + 1, h):
            ks = [tidx[(1 << i) | (1 << j) | (1 << k)] for k in range(j + 1, h)]
            if not ks:
                continue

            def lab(lo, hi, ks=ks):
                X = 0
                for q in ks[lo:hi]:
                    X |= T[q]
                return ('coord', X)
            r, _ = balanced(C, ks, lab, 'global')
            lvl2.append(r)
        if not lvl2:
            continue
        lvl1.append(balanced_by_union(C, lvl2, 'global'))
    Cstar = balanced_by_union(C, lvl1, 'global')
    C.global_adds = C.n_nodes() - n0
    # ----- fixed-pair trees ------------------------------------------------
    n0 = C.n_nodes()
    pair_root = {}
    pair_q = 0
    for i, j in combinations(range(h), 2):
        Pm = (1 << i) | (1 << j)
        ks = [k for k in range(h) if k not in (i, j)]
        leaves = [tidx[Pm | (1 << k)] for k in ks]

        def lab(lo, hi, ks=ks, Pm=Pm):
            lam = 0
            for k in ks[lo:hi]:
                lam |= 1 << k
            return ('star', Pm, lam)
        root, info = balanced(C, leaves, lab, 'pair')
        pair_root[(i, j)] = root
        # selection for each target P+{r}
        for ri, r in enumerate(ks):
            z = root
            sel = []
            while True:
                lo, hi, a, b = info[z]
                if a is None:
                    break
                la = info[a]
                if la[0] <= ri < la[1]:
                    sel.append(b)
                    z = a
                else:
                    sel.append(a)
                    z = b
            assert info[z][0] == ri
            for zz in sel:
                C.outputs.append((zz, tidx[Pm | (1 << r)], -HALF))
                pair_q += 1
    C.pair_adds = C.n_nodes() - n0
    C.pair_q = pair_q
    # ----- point totals D_i, i < h-1 ----------------------------------
    n0 = C.n_nodes()
    Dnode = {}
    for i in range(h - 1):
        roots = [pair_root[(min(i, j), max(i, j))] for j in range(h) if j != i]
        r, _ = balanced(C, roots, lambda lo, hi, i=i: ('S', i), 'point')
        Dnode[i] = r
    C.point_adds = C.n_nodes() - n0
    for i in range(h - 1):
        C.outputs.append((Dnode[i], ('tot', i), Fraction(1)))
    C.outputs.append((Cstar, ('tot', '*'), Fraction(1)))
    C.q0 = rect_outs
    return C


def balanced_by_union(C, nodes, family):
    """Balanced tree over already-built coordinate nodes."""
    T = C.T

    def pts(z):
        if C.kind[z] == 'in':
            return T[C.args[z]]
        return C.label[z][1]

    def rec(lo, hi):
        if hi - lo == 1:
            return nodes[lo]
        mid = lo + (hi - lo) // 2
        a, b = rec(lo, mid), rec(mid, hi)
        return C.add(a, b, family, ('coord', pts(a) | pts(b)))
    return rec(0, len(nodes))


def label_space(C, key, Space):
    h = C.h
    k = key[0]
    if k == 'coord':
        return Space(h, [1 << p for p in range(h) if key[1] >> p & 1])
    if k == 'star':
        Pm, lam = key[1], key[2]
        return Space(h, [Pm | (1 << u) for u in range(h) if lam >> u & 1])
    if k == 'S':
        i = key[1]
        c = (1 << h) - 1
        return Space(h, [c ^ (1 << k2) for k2 in range(h) if k2 != i])
    raise ValueError(key)


def scatter_rows(C):
    """Exact retained-total scatter R as {target: {total tag: coeff}}."""
    h = C.h
    rows = {}
    for si, S in enumerate(C.T):
        r = {}
        if not (S >> (h - 1)) & 1:
            for i in range(h):
                if S >> i & 1:
                    r[('tot', i)] = QUARTER
            r[('tot', '*')] = -HALF
        else:
            r[('tot', '*')] = Fraction(1)
            for i in range(h - 1):
                if not S >> i & 1:
                    r[('tot', i)] = -QUARTER
        rows[si] = r
    return rows


def check_map(C):
    """(R + J) L V == I exactly, using actual integer multiplicities."""
    sup = C.supports()
    tot = {}
    side = {}
    for z, t, c in C.outputs:
        if isinstance(t, tuple):
            tot[t] = sup[z]
        else:
            row = side.setdefault(t, {})
            for s, m in sup[z].items():
                row[s] = row.get(s, 0) + c * m
    rows = scatter_rows(C)
    fails = []
    nnz_side = 0
    for si in range(C.v):
        acc = dict(side.get(si, {}))
        nnz_side += sum(1 for x in acc.values() if x)
        for tag, c in rows[si].items():
            for s, m in tot[tag].items():
                acc[s] = acc.get(s, 0) + c * m
        for ti in range(C.v):
            want = 1 if ti == si else 0
            if acc.get(ti, 0) != want:
                fails.append((si, ti, acc.get(ti, 0)))
                if len(fails) > 20:
                    return False, nnz_side, fails
    return not fails, nnz_side, fails
