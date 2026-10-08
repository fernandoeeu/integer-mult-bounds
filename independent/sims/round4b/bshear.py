"""End-to-end address-level simulation of the batched interchange recursion
(projector-batching.tex + batched-bit-rows.tex 'Bit interchange with a
remainder'), built from the notes, on a toy one-role circuit whose single
wire passes through the frames of one structured class (h=3, m=27), all
conjugated by one controlled basis S.  A child interchange is executed by
the same recursion (no oracle) down to width < m.  For random addresses we
compare the final address with the exact interchange of the two chunks,
and check every spectator digit.  Exact modular arithmetic.
Not modelled: row split into W role streams (W=1 here), padding rows,
fixed-tape scheduling (they do not change the address map)."""
import sys, random, time
from fractions import Fraction as Q
from lin import *
from family import instances, controlled_S

MUT = None   # negative controls: 'misalign', 'nomiddleupdate', 'swaporder'

def is_prime(n): return n > 1 and all(n % p for p in range(2, int(n**.5)+1))

class Edge:
    def __init__(self, A):
        m = len(A); self.m = m
        a = rank(A); self.a = a
        E1, Pi, E2, piv = lower_lower(A)
        self.E1, self.E2, self.E1i, self.E2i = E1, E2, inv(E1), inv(E2)
        r = m - a
        self.groups = []                 # ('s', i, j) or ('b', i0, j0, t)
        prof, matched = classify_pivots(piv, m, a) if 2*a > m and a < m else (False, False)
        self.kind = 'unbatched'
        if prof:
            if matched and r > 1:
                self.groups.append(('b', 0, m-r, r)); self.kind = 'corner-block+middle'
            else:
                for i, j in piv[:r]: self.groups.append(('s', i, j)); self.kind = 'singletons+middle'
            self.groups.append(('b', r, r, m-2*r))
        else:
            for i, j in piv: self.groups.append(('s', i, j))
        self.children = [g[3] if g[0] == 'b' else 1 for g in self.groups]
    def denoms(self):
        out = set()
        for X in (self.E1, self.E2, self.E1i, self.E2i):
            for r in X:
                for x in r: out.add(x.denominator)
            for i in range(self.m): out.add(abs(X[i][i].numerator))
        return out

class Sim:
    def __init__(self, edges, q):
        self.edges, self.q = edges, q; self.m = edges[0].m
        self.nodes = 0; self.maxdepth = 0
    # ---- digit helpers; field value = little-endian within the field
    def getf(self, x, p, f):
        v = 0
        for k in range(f): v += x[p+k] * self.q**k
        return v
    def setf(self, x, p, f, v):
        v %= self.q**f
        for k in range(f): x[p+k] = v % self.q; v //= self.q
    def lin(self, x, p, f, E, mod):
        """apply rational lower-triangular E to the m fields at p (width f)"""
        vals = [self.getf(x, p + k*f, f) for k in range(self.m)]
        out = []
        for i in range(self.m):
            s = 0
            for j in range(i+1):
                c = E[i][j]
                if c: s += (c.numerator * pow(c.denominator, -1, mod)) * vals[j]
            out.append(s % mod)
        for i in range(self.m): self.setf(x, p + i*f, f, out[i])
    def shear(self, x, ph, pd, f, edge, depth):
        """(H,D) -> (H + A D, D) on m fields of width f"""
        mod = self.q**f
        self.lin(x, pd, f, edge.E2, mod); self.lin(x, ph, f, edge.E1i, mod)
        for g in edge.groups:
            if g[0] == 's':
                _, i, j = g; t = 1; i0, j0 = i, j
            else:
                _, i0, j0, t = g
                if MUT == 'misalign' and t > 1 and i0 == j0: j0 = j0 + 1 if j0 + t < self.m else j0 - 1
            for k in range(t):           # D_j <- D_j + H_i  (componentwise mod q^f)
                if MUT == 'nomiddleupdate' and t > 1 and k == 0: continue
                self.setf(x, pd+(j0+k)*f, f, self.getf(x, pd+(j0+k)*f, f) + self.getf(x, ph+(i0+k)*f, f))
            self.interchange(x, ph + i0*f, pd + j0*f, t*f, depth+1)   # ONE child of width t*f
            for k in range(t):           # D_j <- H_i - D_j
                self.setf(x, pd+(j0+k)*f, f, self.getf(x, ph+(i0+k)*f, f) - self.getf(x, pd+(j0+k)*f, f))
        self.lin(x, ph, f, edge.E1, mod); self.lin(x, pd, f, edge.E2i, mod)
    def interchange(self, x, ph, pd, e, depth=0):
        self.nodes += 1; self.maxdepth = max(self.maxdepth, depth)
        assert ph + e <= pd
        m = self.m
        if e < m:
            for k in range(e): x[ph+k], x[pd+k] = x[pd+k], x[ph+k]
            return
        f, r = divmod(e, m)
        # layout (H+,H-,G,D+,D-), H+ = first r digits of the H chunk
        g = pd - (ph + e)
        Hp = x[ph:ph+r]; Dp = x[pd:pd+r]
        # exchange digits of H+, D+ ; then move H+ (now sitting in D+'s slot) just before H-
        seg = x[ph:pd+e]                 # H+,H-,G,D+,D-
        Hm = seg[r:e]; Gs = seg[e:e+g]; Dm = seg[e+g+r:]
        new = Dp + Hp + Hm + Gs + Dm     # (D+,H+,H-,G,D-)
        x[ph:pd+e] = new
        ph2 = ph + 2*r; pd2 = ph + 2*r + m*f + g
        assert x[ph2:ph2+m*f] == Hm and x[pd2:pd2+m*f] == Dm
        # main interchange of H-, D- by the circuit: D<-D-H ; H<-H+D (shears) ; D<-H-D
        mod = self.q**f
        for k in range(m): self.setf(x, pd2+k*f, f, self.getf(x, pd2+k*f, f) - self.getf(x, ph2+k*f, f))
        for edge in self.edges: self.shear(x, ph2, pd2, f, edge, depth)
        for k in range(m): self.setf(x, pd2+k*f, f, self.getf(x, ph2+k*f, f) - self.getf(x, pd2+k*f, f))
        # now (D+,H+,D-,G,H-) ; move H+ back immediately before the final H-
        seg = x[ph:pd+e]
        Dp2 = seg[:r]; Hp2 = seg[r:2*r]; Dm2 = seg[2*r:2*r+m*f]; Gs2 = seg[2*r+m*f:2*r+m*f+g]; Hm2 = seg[2*r+m*f+g:]
        x[ph:pd+e] = Dp2 + Dm2 + Gs2 + Hp2 + Hm2

def build(h, cls, seed):
    rng = random.Random(seed)
    inst, G = instances(h, rng, n_each=1)
    S, Si = controlled_S(h, rng)
    chain = next(c for k, A, c in inst if k == cls)
    if cls == 'neg':
        pass
    frames = [mul(mul(S, M), Si) for M in chain]
    edges = [Edge(add(frames[i+1], frames[i], -1)) for i in range(len(frames)-1)]
    return edges, frames

def run(cls, widths, seed=1, trials=3, h=3):
    edges, frames = build(h, cls, seed)
    m = h**3
    assert add(frames[-1], frames[0], -1) == eye(m), 'endpoint identity'
    den = set().union(*[e.denoms() for e in edges])
    q = next(p for p in range(11, 10**6) if is_prime(p) and all(d % p for d in den if d))
    sim = Sim(edges, q)
    info = [(e.a, e.kind, sorted(set(e.children))) for e in edges]
    rng = random.Random(seed + 7)
    allok = True
    for e in widths:
        for _ in range(trials):
            pre, gap, post = rng.randint(0, 3), rng.randint(0, 5), rng.randint(0, 3)
            n = pre + e + gap + e + post
            x = [rng.randrange(q) for _ in range(n)]
            want = x[:pre] + x[pre+e+gap:pre+2*e+gap] + x[pre+e:pre+e+gap] + x[pre:pre+e] + x[pre+2*e+gap:]
            sim.interchange(x, pre, pre + e + gap, e)
            allok &= x == want
    return allok, q, info, sim.nodes, sim.maxdepth

if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1].startswith('--mut='): MUT = sys.argv[1][6:]
    t0 = time.time(); OK = True
    widths = [26, 27, 28, 53, 54, 55, 81, 100, 135, 163, 243] if MUT else [1, 2, 26, 27, 28, 29, 53, 54, 55, 80, 81, 82, 100, 135, 163, 243, 378, 500, 729, 731]
    for cls in ('A1', 'A2', 'A3'):
      for seed in ((1,) if MUT else (1, 2, 3)):
        ok, q, info, nodes, depth = run(cls, widths, seed=seed)
        OK &= ok
        print(('PASS ' if ok else 'FAIL ') + f'{cls} seed {seed}: batched recursive interchange = exact chunk swap, spectators kept; widths {widths}; q={q}; edges(rank,kind,child t-values)={info}; nodes={nodes}, maxdepth={depth} ({time.time()-t0:.0f}s)')
        sys.stdout.flush()
    print('ALL PASS' if OK else ('SOME FAIL' + (f' (mutant {MUT})' if MUT else '')))
