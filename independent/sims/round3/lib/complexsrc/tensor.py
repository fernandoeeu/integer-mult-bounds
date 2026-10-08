"""Full tensor-level check of one invocation per stage, small h.

Every frame is materialized as an actual subspace of F^{(x)3} = F_2^{h^3}
(standard dot product = tensor form), with the upstream stage decomposition
A = B _|_ P and future line Q built from concrete fixed triples.  This checks
the factored F-level reasoning instead of assuming it.
"""
import random
from f2 import Space, perp, residual, nondegenerate, nonalternating, orthonormal_basis, check_orthonormal, norm
from network import walk, Labels, F_KEY, Z_KEY


def tens(x, y, z, h):
    out = 0
    for i in range(h):
        if not x >> i & 1:
            continue
        for j in range(h):
            if not y >> j & 1:
                continue
            base = (i * h + j) * h
            for k in range(h):
                if z >> k & 1:
                    out |= 1 << (base + k)
    return out


def tens2(xy, z, h):
    """xy: vector of F(x)F as int over h^2 bits (index i*h+j)."""
    out = 0
    for ij in range(h * h):
        if xy >> ij & 1:
            base = ij * h
            for k in range(h):
                if z >> k & 1:
                    out |= 1 << (base + k)
    return out


class StageFrames:
    def __init__(self, labels, stage, a, h):
        """a = (t1, t2, t3) triple masks of the data index; coordinate
        `stage` varies, the others fix P (earlier) and Q (later)."""
        self.L, self.j, self.h = labels, stage, h
        self.m = h ** 3
        self.cache = {}
        t1, t2, t3 = a
        F = [1 << i for i in range(h)]
        self.Fb = F
        if stage == 1:
            self.Bb = []          # B = 0
            self.Pv = None        # scalar
            self.q = (t2, t3)
        elif stage == 2:
            Bsp = perp(Space(h, [t1]))
            self.Bb = Bsp.basis()
            self.Pv = t1
            self.q = t3
        else:
            # A = F(x)F on h^2 bits, P = <t1 (x) t2>
            p = 0
            for i in range(h):
                if t1 >> i & 1:
                    for jj in range(h):
                        if t2 >> jj & 1:
                            p |= 1 << (i * h + jj)
            self.Bb = perp(Space(h * h, [p])).basis()
            self.Pv = p

    def place(self, aval, f):
        """aval in A (int over A's bits), f in F -> vector of F^{(x)3}."""
        h, j = self.h, self.j
        if j == 1:
            return tens(f, self.q[0], self.q[1], h)
        if j == 2:
            return tens(aval, f, self.q, h)
        return tens2(aval, f, h)

    def frame(self, fr):
        sp = self.cache.get(fr)
        if sp is not None:
            return sp
        if fr == 'FULL':
            sp = Space(self.m, [1 << i for i in range(self.m)])
            self.cache[fr] = sp
            return sp
        bk, pk = fr
        Bp = self.L.space(bk).basis()
        Pp = self.L.space(pk).basis()
        vecs = []
        for b in self.Bb:
            for f in Bp:
                vecs.append(self.place(b, f))
        for f in Pp:
            vecs.append(self.place(self.Pv if self.j > 1 else None, f))
        sp = Space(self.m, vecs)
        self.cache[fr] = sp
        return sp


class TensorChecker:
    def __init__(self, sf, full_onb_sample=1.0, rng=None):
        self.sf = sf
        self.cache = {}
        self.nd_cache = {}
        self.sample = full_onb_sample
        self.rng = rng or random.Random(5)
        self.n_onb = 0

    def nd(self, fr):
        r = self.nd_cache.get(fr)
        if r is None:
            r = nondegenerate(self.sf.frame(fr))
            self.nd_cache[fr] = r
        return r

    def edge(self, f1, f2):
        key = (f1, f2)
        r = self.cache.get(key)
        if r is not None:
            return r
        U, V = self.sf.frame(f1), self.sf.frame(f2)
        if not self.nd(f1) or not self.nd(f2):
            r = (False, 0, 'degenerate label')
        else:
            if V.contains_space(U):
                small, big, sign = U, V, 1
            elif U.contains_space(V):
                small, big, sign = V, U, -1
            else:
                r = (False, 0, 'incomparable')
                self.cache[key] = r
                return r
            E = residual(small, big)
            d = E.dim()
            if d == 0:
                r = (True, 0, '')
            elif not nondegenerate(E):
                r = (False, 0, 'degenerate residual')
            elif not nonalternating(E):
                r = (False, 0, 'alternating residual')
            else:
                ok = True
                if self.rng.random() < self.sample:
                    ob = orthonormal_basis(E)
                    self.n_onb += 1
                    ok = ob is not None and check_orthonormal(ob, E)
                r = (ok, sign * d, '' if ok else 'onb failed')
        self.cache[key] = r
        return r


def check_stage(inv, labels, stage, a, sample=1.0):
    h = labels.h
    sf = StageFrames(labels, stage, a, h)
    tc = TensorChecker(sf, sample)
    seq = walk(inv)
    fails, tot_abs, dec = [], 0, []
    first, last = {}, {}
    v = inv.v
    for w in range(inv.nw):
        frames = [f for f, _ in seq[w]]
        is_aux = w >= 2 * v
        if is_aux:
            chain = [(Z_KEY, Z_KEY)] + frames + ['FULL']
            first[w] = frames[0]
            last[w] = frames[-1]
        else:
            T = w if w < v else w - v
            if w < v:
                chain = [(('line', T), ('line', T))] + frames + [(F_KEY, F_KEY)]
            else:
                chain = [(('line', T), Z_KEY)] + frames + [(F_KEY, ('tperp', T))]
        for i in range(len(chain) - 1):
            ok, d, why = tc.edge(chain[i], chain[i + 1])
            if not ok:
                fails.append((w, i, chain[i], chain[i + 1], why))
                continue
            tot_abs += abs(d)
            if d < 0:
                dec.append((w, -d))
    return dict(fails=fails, tot_abs=tot_abs, dec=dec, first=first, last=last,
                sf=sf, n_res=len(tc.cache), n_onb=tc.n_onb)


def data_terminal_consistency(labels, h, a):
    """Upstream interstage boundary: outgoing labels of stage j equal the
    incoming labels of stage j+1 (checked as subspaces of F^{(x)3})."""
    out = []
    for j in (1, 2):
        s1 = StageFrames(labels, j, a, h)
        s2 = StageFrames(labels, j + 1, a, h)
        tj = [a[0], a[1], a[2]][j - 1]
        tn = [a[0], a[1], a[2]][j]
        Tj = labels.C.tidx[tj]
        Tn = labels.C.tidx[tn]
        X_out = s1.frame((F_KEY, F_KEY))
        X_in = s2.frame((('line', Tn), ('line', Tn)))
        Y_out = s1.frame((F_KEY, ('tperp', Tj)))
        Y_in = s2.frame((('line', Tn), Z_KEY))
        out.append((j, X_out == X_in, Y_out == Y_in))
    # stage-1 sources and stage-3 sinks
    s1 = StageFrames(labels, 1, a, h)
    s3 = StageFrames(labels, 3, a, h)
    ua = tens(a[0], a[1], a[2], h)
    m = h ** 3
    Ua = Space(m, [ua])
    T1, T3 = labels.C.tidx[a[0]], labels.C.tidx[a[2]]
    out.append(('X source = U_a', s1.frame((('line', T1), ('line', T1))) == Ua, True))
    out.append(('Y source = 0', s1.frame((('line', T1), Z_KEY)).dim() == 0, True))
    out.append(('X sink = full', s3.frame((F_KEY, F_KEY)).dim() == m, True))
    out.append(('Y sink = U_a^perp', s3.frame((F_KEY, ('tperp', T3))) == perp(Ua), True))
    return out
