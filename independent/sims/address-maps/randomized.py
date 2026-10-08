"""Randomised and adversarial checks at larger parameters (Python big ints).

Same checks C1-C8 as exhaustive.py, per sampled address.  Inputs are biased to
the edges named in the text: guard values at 2B-1, 2B, 2^{K-1}-2B-1,
2^{K-1}-2B, 0 and maximal; temporary digits 0, B-2, B-1; rho in {0, K-1};
smallest admissible K for a non-empty good set (K = G+4); n=1; and the
proposition's own parameter shape G = 4 ceil(log2 p)+6, K >= G+4 ceil(log2 p)+10,
f <= p.
"""
import math
import random
import sys
import time

from addrmaps import (Params, make_program, run, run_inverse, ideal, top_xor,
                      full_ideal, bad, segment, digit, bit)


def stepwise(P, st0, ops, good):
    """C5/C6 on one address; returns list of violation strings."""
    errs = []
    where = {k: k for k in st0}
    acc_seg = [0] * P.n
    acc_dig = {lab: [0] * P.n for lab in ('t', 'u', 'b')}
    seg0 = [segment(P, st0['y'], i) for i in range(P.n)]
    dig0 = {lab: [digit(P, st0[lab], i) for i in range(P.n)] for lab in ('t', 'u', 'b')}
    st = dict(st0)
    for op in ops:
        if op[0] == 'swap':
            _, p, q = op
            st[p], st[q] = st[q], st[p]
            where[p], where[q] = where[q], where[p]
            continue
        cap = {}

        def hook(op_, s_, coefs, kind):
            cap['c'] = coefs
            cap['k'] = kind
        st = run(P, st, [op], hook=hook)
        if not good:
            continue
        coefs, kind = cap['c'], cap['k']
        if kind == 'seg':
            for i in range(P.n):
                acc_seg[i] += coefs[i]
                exp = seg0[i] + acc_seg[i]
                if segment(P, st['y'], i) != exp or not (0 <= exp < 1 << P.K) \
                        or abs(acc_seg[i]) > 2 * P.B:
                    errs.append(f"segment {i} after {op[4]}")
        else:
            lab = where[op[1]]
            for i in range(P.n):
                acc_dig[lab][i] += coefs[i]
                exp = dig0[lab][i] + acc_dig[lab][i]
                if digit(P, st[op[1]], i) != exp or not (0 <= exp < P.B):
                    errs.append(f"digit {lab}{i} after {op[4]}")
            if op[4].startswith('(4)'):
                for i in range(P.n):
                    if segment(P, st['y'], i) >> 1 != seg0[i] >> 1:
                        errs.append(f"guard {i} changed")
    return errs


def check(P, late, st0, ops):
    errs = []
    b0 = bool(bad(P, st0, late))
    out = run(P, st0, ops)
    if run_inverse(P, out, ops) != st0:
        errs.append('C1 inverse')
    if out['x'] != st0['x'] or out['b'] != st0['b']:
        errs.append('C10 x or b not restored')
    T = ideal(P, st0)
    if bool(bad(P, T, late)) != b0:
        errs.append('C2 T-invariance')
    bS = bool(bad(P, out, late))
    if bS != b0:
        errs.append('C3 S-invariance')
    if not b0 and out != T:
        errs.append('C4 S!=T on good')
    errs += ['C5/C6 ' + e for e in stepwise(P, st0, ops, not b0)]
    if bS:
        dest = ideal(P, run_inverse(P, out, ops))
        if not bad(P, dest, late):
            errs.append('C8 destination not bad')
        rep = dest
    else:
        rep = out
    if top_xor(P, rep) != full_ideal(P, st0):
        errs.append('C7 repaired != full XOR')
    return b0, errs


def adversarial_state(P, late, rng):
    B, K = P.B, P.K
    gmax = (1 << (K - 1)) - 1
    gchoices = [2 * B - 1, 2 * B, (1 << (K - 1)) - 2 * B - 1, (1 << (K - 1)) - 2 * B,
                0, gmax]
    dchoices = [0, B - 2, B - 1]
    mode = rng.random()
    y = rng.getrandbits(P.W_slot)
    for i in range(P.n):
        r = rng.random()
        lo, hi = 2 * B, (1 << (K - 1)) - 2 * B - 1
        if mode < 0.5 and lo <= hi:
            g = rng.choice([lo, hi, rng.randint(lo, hi)])
        elif r < 0.5:
            g = rng.choice(gchoices)
        elif r < 0.75:
            g = rng.choice([2 * B, (1 << (K - 1)) - 2 * B - 1])   # good boundary
        else:
            g = rng.randrange(gmax + 1)
        g = min(max(g, 0), gmax)
        a = rng.getrandbits(1)
        seg = 2 * g + a
        y = (y & ~(((1 << K) - 1) << P.j[i])) | (seg << P.j[i])

    def cmp_field(bias):
        v = 0
        for i in range(P.n):
            if rng.random() < bias:
                d = rng.choice(dchoices)
            else:
                d = rng.randrange(B)
            d = min(max(d, 0), B - 1)
            if mode < 0.5 and d == B - 1:
                d = max(B - 2, 0)        # good-edge mode: keep the address good
            v |= d << (i * P.G)
        return v
    x = rng.getrandbits(P.W_slot)
    if rng.random() < 0.3:
        x = (1 << P.W_slot) - 1
    st = dict(x=x, y=y, t=cmp_field(0.7), b=rng.choice([0, (1 << P.W_cmp) - 1,
                                                        rng.getrandbits(P.W_cmp)]),
              u=cmp_field(0.7) if late else rng.getrandbits(P.W_cmp))
    return st


def param_list(rng):
    ps = []
    # small K at the edge of a nonempty good set, many f, G
    for G in (1, 2, 3, 5, 8):
        for f in (2, 3, 4, 7, 16):
            for K in (G + 4, G + 5, G + 8, 2 * G + 12):
                for rho in sorted({0, K - 1, rng.randrange(K)}):
                    ps.append(Params(f, K, rho, G))
    # proposition shape: G = 4 l + 6, K = G + 4 l + 10 (the stated cutoff)
    for p in (2, 3, 5, 16, 100, 1000):
        l = math.ceil(math.log2(p))
        G = 4 * l + 6
        K = G + 4 * l + 10
        for f in sorted({2, min(p, 3), p}):
            if f < 2:
                continue
            for rho in (0, K - 1):
                ps.append(Params(f, K, rho, G))
    return ps


def main(samples=300, seed=20261008):
    rng = random.Random(seed)
    t0 = time.time()
    total = good = 0
    failures = []
    for P in param_list(rng):
        for late in (False, True):
            ops = make_program(late)
            ns = samples if P.n <= 16 else max(10, samples // 20)
            for _ in range(ns):
                st0 = adversarial_state(P, late, rng)
                b0, errs = check(P, late, st0, ops)
                total += 1
                good += (not b0)
                if errs:
                    failures.append((P, late, st0, errs[:3]))
                    if len(failures) < 5:
                        print('FAIL', P, late, errs[:3], flush=True)
    print(f"randomized: {total} addresses, {good} good, {total-good} bad, "
          f"{len(failures)} failing; {time.time()-t0:.0f}s")
    return len(failures)


if __name__ == '__main__':
    sys.exit(1 if main() else 0)
