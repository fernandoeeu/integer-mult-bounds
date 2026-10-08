"""Independent builder for PR 6's aligned bit circuit with cheaper centers.

Written from notes/paired-construction.tex (published paired recursion) and
notes/aligned-bit-construction.tex at PR 6 head 5015011 (aligned blocks,
shared top-level pair-star chains, retained group totals). It does not import
or copy the PR's Python.

Representation. Group i works on the points [h] minus i; a group-local formal
sum is a bitmask over the pairs {a,b} of those points (pair {a,b} stands for
the triple {i,a,b}). Equal formal sums are interned globally with a canonical
key that is computed from the actual set of triples:
  * one triple                        -> ('T', triple)
  * >= 2 triples with two common points -> ('S', sorted tuple of triples)
  * otherwise (exactly one common pt)   -> ('G', i, mask)
The first encountered decomposition is kept ("Keep the first encountered
decomposition, in common-point and then local-node order").

Conventions the notes leave open (they change counts, never correctness):
  BAL_SPLIT   balanced addition splits a list of k nonzero terms at k//2;
  zero terms are dropped before splitting;
  w~_A lists vertex weights before internal edges;
  direct base sums list edges before weights (published paired order).
These were chosen from the notes' wording; see run logs for the counts.
"""
from itertools import combinations
import sys


class Builder:
    def __init__(self, h, base=4, conv=None):
        assert h % 2 == 0 and h >= 6
        self.h, self.base = h, base
        self.conv = dict(split='floor', weights_first=True, base_edges_first=True)
        if conv:
            self.conv.update(conv)
        self.trip = list(combinations(range(h), 3))
        self.tid = {t: k for k, t in enumerate(self.trip)}
        # node store: inputs are nodes 0..v-1 (triple index); additions after
        self.left, self.right, self.home, self.hmask = [], [], [], []
        self.key2node = {}
        for k, t in enumerate(self.trip):
            self.key2node[('T', t)] = k
        self.v = len(self.trip)
        self.partial = {}   # (i, T) -> node
        self.center = {}    # i -> node
        for i in range(h):
            self._group(i)
        self._prune()

    # ------------------------------------------------------------ group i
    def _group(self, i):
        h = self.h
        self.i = i
        pts = [p for p in range(h) if p != i]
        self.pts = pts
        self.pidx = {}
        for k, (a, b) in enumerate(combinations(pts, 2)):
            self.pidx[a, b] = self.pidx[b, a] = k
        self.pairs = list(combinations(pts, 2))
        # star masks: pairs containing point j (in this group's coordinates)
        self.star = {j: 0 for j in pts}
        for k, (a, b) in enumerate(self.pairs):
            self.star[a] |= 1 << k
            self.star[b] |= 1 << k
        self.mask2node = {}
        # weighted graph at the top: weights 0, edges x_{iab}
        e = {}
        for a, b in self.pairs:
            e[frozenset((a, b))] = 1 << self.pidx[a, b]
        total, F = self._top(pts, e)
        for a, b in self.pairs:
            T = tuple(sorted((i, a, b)))
            self.partial[i, T] = self._node(F[frozenset((a, b))])
        self.center[i] = self._node(total)

    def _key(self, m):
        i = self.i
        if m & (m - 1) == 0:
            a, b = self.pairs[m.bit_length() - 1]
            return ('T', tuple(sorted((i, a, b))))
        if m.bit_count() <= self.h - 2:
            a, b = self.pairs[(m & -m).bit_length() - 1]
            for j in (a, b):
                if m & ~self.star[j] == 0:
                    trips = []
                    mm = m
                    while mm:
                        lb = mm & -mm
                        mm ^= lb
                        x, y = self.pairs[lb.bit_length() - 1]
                        trips.append(self.tid[tuple(sorted((i, x, y)))])
                    return ('S', tuple(sorted(trips)))
        return ('G', i, m)

    def _node(self, m):
        n = self.mask2node.get(m)
        if n is None:
            n = self.key2node[self._key(m)]
            self.mask2node[m] = n
        return n

    def add(self, x, y):
        """Formal sum of two group-local masks (0 = empty)."""
        if not x:
            return y
        if not y:
            return x
        if x & y:
            raise AssertionError('overlapping supports at an addition')
        m = x | y
        if m in self.mask2node:
            return m
        k = self._key(m)
        n = self.key2node.get(k)
        if n is None:
            n = self.v + len(self.left)
            self.left.append(self._node(x))
            self.right.append(self._node(y))
            self.home.append(self.i)
            self.hmask.append(m)
            self.key2node[k] = n
        self.mask2node[m] = n
        return m

    def bal(self, terms):
        t = [x for x in terms if x]
        if not t:
            return 0
        if len(t) == 1:
            return t[0]
        mid = len(t) // 2 if self.conv['split'] == 'floor' else (len(t) + 1) // 2
        return self.add(self.bal(t[:mid]), self.bal(t[mid:]))

    # ------------------------------------------------------- recursion
    @staticmethod
    def blocks_of(verts):
        by = {}
        for u in verts:
            by.setdefault(u // 2, []).append(u)
        return [(k, by[k]) for k in sorted(by)]

    def solve(self, verts, w, e, need_single=True):
        """Weighted graph: verts ordered; w[u] mask; e[frozenset] mask.
        Returns (total, O[u], F[frozenset{u,v}])."""
        E = lambda a, b: e.get(frozenset((a, b)), 0)
        if len(verts) <= self.base:
            def surv(dead):
                alive = [u for u in verts if u not in dead]
                ws = [w.get(u, 0) for u in alive]
                es = [E(a, b) for a, b in combinations(alive, 2)]
                return self.bal(es + ws if self.conv['base_edges_first'] else ws + es)
            tot = surv(())
            O = {u: surv((u,)) for u in verts}
            F = {frozenset((a, b)): surv((a, b)) for a, b in combinations(verts, 2)}
            return tot, O, F
        blocks = self.blocks_of(verts)
        labs = [k for k, _ in blocks]
        B = dict(blocks)
        wt = {}
        for k in labs:
            inner = [E(a, b) for a, b in combinations(B[k], 2)]
            ws = [w.get(u, 0) for u in B[k]]
            wt[k] = self.bal(ws + inner if self.conv['weights_first'] else inner + ws)
        ce = {}
        for K1, K2 in combinations(labs, 2):
            ce[frozenset((K1, K2))] = self.bal([E(a, b) for a in B[K1] for b in B[K2]])
        tot, O, F = self.solve(labs, wt, ce)
        Hleave, Htot = {}, {}
        for K in labs:
            others = [C for C in labs if C != K]
            for a in B[K]:
                rest = [u for u in B[K] if u != a]
                Ca = self.bal([w.get(u, 0) for u in rest])
                Eac = [self.bal([E(u, c) for u in rest for c in B[C]]) for C in others]
                vec = [Ca] + Eac
                n = len(vec)
                pre = [0] * (n + 1)
                for k in range(n):
                    pre[k + 1] = self.add(pre[k], vec[k])
                suf = [0] * (n + 2)
                for k in range(n - 1, 1, -1):     # only suffixes that are requested
                    suf[k] = self.add(vec[k], suf[k + 1])
                for k in range(1, n):
                    Hleave[a, others[k - 1]] = self.add(pre[k], suf[k + 1])
                Htot[a] = pre[n]
        outF = self._combine(blocks, B, E, F, O, Hleave)
        outO = {}
        if need_single:
            for K in labs:
                for a in B[K]:
                    outO[a] = self.add(O[K], Htot[a])
        return tot, outO, outF

    def _combine(self, blocks, B, E, F, O, Hleave):
        out = {}
        labs = [k for k, _ in blocks]
        blk = {u: k for k, us in blocks for u in us}
        for K in labs:
            for a, b in combinations(B[K], 2):
                out[frozenset((a, b))] = O[K]
        for K1, K2 in combinations(labs, 2):
            for a in B[K1]:
                for b in B[K2]:
                    ra = [u for u in B[K1] if u != a]
                    rb = [u for u in B[K2] if u != b]
                    cross = self.bal([E(u, x) for u in ra for x in rb])
                    first = self.add(F[frozenset((K1, K2))], Hleave[a, K2])
                    second = self.add(Hleave[b, K1], cross)
                    out[frozenset((a, b))] = self.add(first, second)
        return out

    def _top(self, verts, e):
        """Top level of group i with the shared pair-star chains."""
        i = self.i
        E = lambda a, b: e.get(frozenset((a, b)), 0)
        blocks = self.blocks_of(verts)
        labs = [k for k, _ in blocks]
        B = dict(blocks)
        own = i // 2
        wt = {K: self.bal([E(a, b) for a, b in combinations(B[K], 2)]) for K in labs}
        ce = {frozenset((K1, K2)): self.bal([E(a, b) for a in B[K1] for b in B[K2]])
              for K1, K2 in combinations(labs, 2)}
        tot, O, F = self.solve(labs, wt, ce)
        Hleave = {}
        for K in labs:
            for a in B[K]:
                rest = [u for u in B[K] if u != a]
                if not rest:
                    for J in labs:
                        if J != K:
                            Hleave[a, J] = 0
                    continue
                (q,) = rest
                common = [C for C in labs if C not in (K, own)]
                vals = [self.bal([E(q, c) for c in B[C]]) for C in common]
                n = len(vals)
                pre = [0] * (n + 1)
                for k in range(n):
                    pre[k + 1] = self.add(pre[k], vals[k])
                suf = [0] * (n + 2)
                for k in range(n - 1, 0, -1):
                    suf[k] = self.add(vals[k], suf[k + 1])
                extra = self.bal([E(q, c) for c in B[own]]) if K != own else 0
                for k, C in enumerate(common):
                    Hleave[a, C] = self.add(self.add(pre[k], suf[k + 1]), extra)
                if K != own:
                    Hleave[a, own] = pre[n]
        return tot, self._combine(blocks, B, E, F, O, Hleave)

    # ------------------------------------------------------------ prune
    def _prune(self):
        v = self.v
        live = set()
        stack = list(self.partial.values()) + list(self.center.values())
        while stack:
            n = stack.pop()
            if n in live:
                continue
            live.add(n)
            if n >= v:
                stack.append(self.left[n - v])
                stack.append(self.right[n - v])
        self.created = len(self.left)
        remap = list(range(v))
        L, R, H, M = [], [], [], []
        remap += [-1] * len(self.left)
        for k in range(len(self.left)):
            n = v + k
            if n not in live:
                continue
            remap[n] = v + len(L)
            L.append(remap[self.left[k]])
            R.append(remap[self.right[k]])
            H.append(self.home[k])
            M.append(self.hmask[k])
        self.left, self.right, self.home, self.hmask = L, R, H, M
        self.partial = {k: remap[n] for k, n in self.partial.items()}
        self.center = {k: remap[n] for k, n in self.center.items()}
        self.c = len(L)

    def graph(self):
        """Export: what the verifier is allowed to see."""
        return dict(h=self.h, v=self.v, left=self.left, right=self.right,
                    partial=[(n, i, T) for (i, T), n in sorted(self.partial.items())],
                    center=[(n, i) for i, n in sorted(self.center.items())])


if __name__ == '__main__':
    for h in map(int, sys.argv[1:]):
        b = Builder(h)
        print(h, 'additions', b.c, 'partial', len(b.partial), 'centers', len(b.center),
              'R=c+q+h', b.c + len(b.partial) + len(b.center), 'created', b.created)
