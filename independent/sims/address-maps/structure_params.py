"""Structural and parameter claims around the address maps.

S1  Physical order: every rotation's control positions precede its target,
    for every admissible order of the fields named in the text:
      earlier source: u,t (either order) < x < y < b
      later source:   u,t (either order) < y < x < b
    (spectators may intervene; they do not change precedence).
S2  Operation counts: earlier 4 swaps / 4 rotations; later 12 swaps / 10
    rotations; every swap is between equal-width compact fields.
S3  Offsets read only declared controls (enforced dynamically in addrmaps.run
    by a guarded view; exercised here on random states).
S4  Proposition: with l=ceil(log2 p), G=4l+6, K>=G+4l+10, f<=p, the late
    bound delta=min{1,n(2*2^-G+8*2^(G-K))} is <= 5/(128 p^3).  Exact
    rational check at the worst case K=G+4l+10, f=p, p=2..200000.
S5  The low n segments [j_i, j_i+K) are disjoint and lie in [0, fK) for
    every rho in [0,K) (checked for K<=40, f<=12).
S6  Layout carving (compact-control-layout.tex): with H=dG, q_F=ceil(2H/K),
    q_B=ceil(H/K): q_F K >= 2H, q_B K >= H, and nG=(f-1)G <= H whenever
    f <= d+1.  Checked over a grid of d, K, p.
"""
import itertools
import math
import random
import sys
from fractions import Fraction

from addrmaps import Params, make_program, run, delta


def s1_s2():
    errs = []
    for late in (False, True):
        ops = make_program(late)
        orders = ([['u', 't', 'x', 'y', 'b'], ['t', 'u', 'x', 'y', 'b']] if not late else
                  [['u', 't', 'y', 'x', 'b'], ['t', 'u', 'y', 'x', 'b']])
        for order in orders:
            for op in ops:
                if op[0] == 'rot':
                    if not all(order.index(c) < order.index(op[1]) for c in op[2]):
                        errs.append(f"S1 late={late} order={order}: {op[4]} control after target")
        nsw = sum(o[0] == 'swap' for o in ops)
        nrot = sum(o[0] == 'rot' for o in ops)
        want = (12, 10) if late else (4, 4)
        if (nsw, nrot) != want:
            errs.append(f"S2 late={late}: {nsw} swaps {nrot} rotations, text says {want}")
        for o in ops:
            if o[0] == 'swap' and not {o[1], o[2]} <= {'u', 't', 'b'}:
                errs.append(f"S2 swap of non-compact fields {o}")
    return errs


def s3(rng):
    errs = []
    for _ in range(200):
        P = Params(rng.randint(2, 6), rng.randint(5, 20), 0, rng.randint(1, 4))
        P = Params(P.f, P.K, rng.randrange(P.K), P.G)
        late = rng.random() < 0.5
        st = {k: rng.getrandbits(P.width(k)) for k in ('x', 'y', 'u', 't', 'b')}
        try:
            run(P, st, make_program(late))
        except KeyError as e:
            errs.append(f"S3 {e}")
    return errs


def s4():
    errs = []
    worst = Fraction(0)
    for p in range(2, 200001):
        l = math.ceil(math.log2(p))
        if (1 << l) < p or (l > 0 and (1 << (l - 1)) >= p):
            errs.append(f"S4 log2 ceiling wrong at {p}")
        G = 4 * l + 6
        K = G + 4 * l + 10
        n = p          # f <= p gives n <= p-1; n = p is the stronger test (repo uses n=p)
        d = min(Fraction(1), n * (Fraction(2, 1 << G) + Fraction(8 << G, 1 << K)))
        bound = Fraction(5, 128 * p ** 3)
        r = d / bound
        worst = max(worst, r)
        if d > bound:
            errs.append(f"S4 delta>{bound} at p={p}")
    return errs, worst


def s5():
    errs = []
    for K in range(1, 41):
        for f in range(2, 13):
            for rho in range(K):
                P = Params(f, K, rho, 1)
                segs = [(P.j[i], P.j[i] + K) for i in range(P.n)]
                if any(a < 0 or b > f * K for a, b in segs):
                    errs.append(f"S5 segment outside y {P}")
                if any(segs[i][1] > segs[i + 1][0] for i in range(len(segs) - 1)):
                    errs.append(f"S5 overlap {P}")
                if P.j[P.n] >= f * K:
                    errs.append(f"S5 top selected bit outside y {P}")
    return errs


def s6():
    errs = []
    for p in (2, 3, 16, 100, 1000, 10 ** 6):
        l = math.ceil(math.log2(p))
        G = 4 * l + 6
        for d in range(1, 300):
            H = d * G
            for K in range(1, 200, 7):
                qF = -(-2 * H // K)
                qB = -(-H // K)
                if qF * K < 2 * H or qB * K < H:
                    errs.append(f"S6 carving fails p={p} d={d} K={K}")
            for f in range(1, d + 2):
                if (f - 1) * G > H:
                    errs.append(f"S6 nG>H p={p} d={d} f={f}")
    return errs


def main():
    rng = random.Random(7)
    errs = s1_s2()
    print(f"S1/S2 physical order and counts: {len(errs)} errors", *errs, sep='\n  ')
    e3 = s3(rng)
    print(f"S3 offsets read only declared controls (200 random runs): {len(e3)} errors")
    e4, worst = s4()
    print(f"S4 delta <= 5/(128 p^3) for p=2..200000 at K=G+4l+10, n=p: {len(e4)} errors; "
          f"max delta/bound = {worst} = {float(worst):.6f}")
    e5 = s5()
    print(f"S5 segment geometry K<=40, f<=12, all rho: {len(e5)} errors")
    e6 = s6()
    print(f"S6 layout carving inequalities: {len(e6)} errors")
    return len(errs) + len(e3) + len(e4) + len(e5) + len(e6)


if __name__ == '__main__':
    sys.exit(1 if main() else 0)
