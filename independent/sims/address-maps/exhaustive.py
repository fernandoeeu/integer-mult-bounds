"""Exhaustive (vectorised) checks of the compact-control address maps.

Mode 'full'      : every address of the rectangle x,y,(u),t,b.
Mode 'structured': every value of y, t, b, (u) and of the f selected bits of
                   x; the other x bits are held at each of three backgrounds
                   (0, all ones, a fixed pseudo-random pattern).  By the
                   text, no offset reads unselected x bits (enforced in the
                   implementation only by construction; preservation of those
                   bits is still checked).

Checks, for every enumerated address a (S = actual sequence, T = ideal):
  C1  S^{-1}(S a) == a                      (bijection + inverse identity)
  C2  bad(T a) == bad(a)                    (ideal map preserves bad set)
  C3  bad(S a) == bad(a)                    (actual map preserves bad set)
  C4  a good  ->  S a == T a                (all fields: x,u,t,b restored)
  C5  a good  ->  at every step each wide segment equals its initial value
                  plus the integer sum of the displayed coefficients, stays in
                  [0,2^K), |displacement| <= 2B; each temporary digit equals
                  initial + integer coefficients and stays in [0,B)
  C6  a good  ->  guard g_i unchanged after each completed four-step identity
  C7  repaired(a) == full XOR at all f selected positions, everything else
                  restored (repair destination T(S^{-1} q) on current bad q)
  C8  T S^{-1} maps current bad addresses to bad addresses
  C9  exact bad count <= delta * count  (bad fraction bound)
  C10 x and b restored by S on every address, good or bad
"""
import sys
import time
from fractions import Fraction
import numpy as np

from addrmaps import (Params, make_program, run, run_inverse, ideal, top_xor,
                      full_ideal, bad, delta, segment, digit, bit)

CHUNK = 1 << 20


def fields_from_index(P, idx, late, mode, bg):
    """Decode a flat index array into field arrays."""
    st = {}
    r = idx.copy()

    def take(nbits):
        nonlocal r
        v = r & ((1 << nbits) - 1)
        r = r >> nbits
        return v
    st['y'] = take(P.W_slot)
    if mode == 'full':
        st['x'] = take(P.W_slot)
    else:
        sel = take(P.f)
        x = np.full_like(idx, bg)
        for i in range(P.f):
            x = (x & ~np.int64(1 << P.j[i])) | (((sel >> i) & 1) << P.j[i])
        st['x'] = x
    st['t'] = take(P.W_cmp)
    st['b'] = take(P.W_cmp)
    if late:
        st['u'] = take(P.W_cmp)
    else:
        st['u'] = np.zeros_like(idx)     # spectator, never touched
    return st


def total_bits(P, late, mode):
    xb = P.W_slot if mode == 'full' else P.f
    return P.W_slot + xb + (3 if late else 2) * P.W_cmp


def check_chunk(P, late, st0, ops, stats):
    good = ~(bad(P, st0, late).astype(bool))
    # ---- C5/C6 instrumentation: follow logical contents through swaps
    where = {k: k for k in st0}          # position -> logical label
    acc_seg = [np.zeros_like(st0['y']) for _ in range(P.n)]
    acc_dig = {lab: [np.zeros_like(st0['y']) for _ in range(P.n)]
               for lab in ('t', 'u', 'b')}
    seg0 = [segment(P, st0['y'], i) for i in range(P.n)]
    dig0 = {lab: [digit(P, st0[lab], i) for i in range(P.n)] for lab in ('t', 'u', 'b')}
    viol = np.zeros(st0['y'].shape, dtype=bool)

    def hook(op, st, coefs, kind):
        nonlocal viol
        tgt = op[1]
        if kind == 'seg':
            assert tgt == 'y' and where['y'] == 'y'
            for i in range(P.n):
                acc_seg[i] = acc_seg[i] + coefs[i]
                cur = segment(P, st['y'], i)
                exp = seg0[i] + acc_seg[i]
                bad_i = (cur != exp) | (exp < 0) | (exp >= (1 << P.K)) | \
                        (np.abs(acc_seg[i]) > 2 * P.B)
                viol |= good & bad_i
            if op[4].startswith('(3)'):
                pass
        else:
            lab = where[tgt]
            for i in range(P.n):
                acc_dig[lab][i] = acc_dig[lab][i] + coefs[i]
                cur = digit(P, st[tgt], i)
                exp = dig0[lab][i] + acc_dig[lab][i]
                viol |= good & ((cur != exp) | (exp < 0) | (exp >= P.B))
            if op[4].startswith('(4)'):
                # end of a four-step identity: guard unchanged (C6)
                for i in range(P.n):
                    viol |= good & ((segment(P, st['y'], i) >> 1) != (seg0[i] >> 1))

    # wrap swaps so the hook knows where contents are
    st = dict(st0)
    for op in ops:
        if op[0] == 'swap':
            _, p, q = op
            st[p], st[q] = st[q], st[p]
            where[p], where[q] = where[q], where[p]
        else:
            st = run(P, st, [op], hook=hook)
    out = st
    stats['C5C6'] += int(viol.sum())

    back = run_inverse(P, out, ops)
    stats['C1'] += int(sum((back[k] != st0[k]).sum() for k in st0))
    T = ideal(P, st0)
    b0 = bad(P, st0, late).astype(bool)
    stats['C2'] += int((bad(P, T, late).astype(bool) != b0).sum())
    bS = bad(P, out, late).astype(bool)
    stats['C3'] += int((bS != b0).sum())
    stats['C4'] += int(sum(((out[k] != T[k]) & good).sum() for k in st0))
    # repair: for current bad q, destination T(S^{-1} q)
    dest = ideal(P, run_inverse(P, out, ops))
    stats['C8'] += int((bS & ~bad(P, dest, late).astype(bool)).sum())
    rep = {k: np.where(bS, dest[k], out[k]) for k in out}
    rep = top_xor(P, rep)
    F = full_ideal(P, st0)
    stats['C7'] += int(sum((rep[k] != F[k]).sum() for k in st0))
    # C10: x and the original back-field contents b are restored on EVERY
    # address (the text: "The arbitrary original contents of b return after
    # each pair of swaps"; x is never a rotation target)
    stats['C10'] += int(((out['x'] != st0['x']) | (out['b'] != st0['b'])).sum())
    stats['count'] += int(st0['y'].size)
    stats['bad'] += int(b0.sum())


def run_config(P, late, mode, bgs=(0,)):
    ops = make_program(late)
    nb = total_bits(P, late, mode)
    stats = dict(count=0, bad=0, C1=0, C2=0, C3=0, C4=0, C5C6=0, C7=0, C8=0, C10=0)
    for bg in bgs:
        for start in range(0, 1 << nb, CHUNK):
            idx = np.arange(start, min(start + CHUNK, 1 << nb), dtype=np.int64)
            st0 = fields_from_index(P, idx, late, mode, bg)
            check_chunk(P, late, st0, ops, stats)
    d = delta(P, late)
    per_bg = stats['count'] // len(bgs)
    stats['C9'] = int(Fraction(stats['bad'] // len(bgs), per_bg) > d)
    stats['delta'] = d
    stats['bad_fraction'] = Fraction(stats['bad'] // len(bgs), per_bg)
    return stats


def configs():
    out = []
    # full rectangles, every rho
    for K in (2, 3, 4, 5):
        for rho in range(K):
            out.append(('full', Params(2, K, rho, 1)))
    # structured
    for (f, K, G) in ((2, 6, 2), (2, 7, 2), (2, 8, 2), (2, 7, 3), (3, 5, 1), (3, 6, 1),
                      (4, 5, 1)):
        for rho in sorted({0, K // 2, K - 1}):
            out.append(('structured', Params(f, K, rho, G)))
    return out


def main(part=None):
    """part None: all configurations; part 1 or 2: alternate halves, so that
    each invocation stays under ~20 minutes on a shared 2-core machine."""
    budget_bits = 24
    t0 = time.time()
    fails = 0
    ncases = 0
    print(f"{'mode':10s} {'late':5s} {'params':24s} {'cases':>10s} {'bad':>9s} "
          f"{'badfrac':>9s} {'delta':>9s} C1 C2 C3 C4 C5C6 C7 C8 C9 C10")
    for k, (mode, P) in enumerate(configs()):
        if part is not None and k % 2 != part - 1:
            continue
        for late in (False, True):
            if total_bits(P, late, mode) > budget_bits:
                continue
            nb = total_bits(P, late, mode)
            bgs = (0,) if mode == 'full' else (
                (0, -1, 0x5A5A5A5A5A5A5A5) if nb <= 22 else (0x5A5A5A5A5A5A5A5,))
            if mode == 'structured':
                bgs = tuple(b & ((1 << P.W_slot) - 1) for b in bgs)
            s = run_config(P, late, mode, bgs)
            ncases += s['count']
            errs = [s[c] for c in ('C1', 'C2', 'C3', 'C4', 'C5C6', 'C7', 'C8', 'C9', 'C10')]
            fails += sum(1 for e in errs if e)
            print(f"{mode:10s} {str(late):5s} {str(P):24s} {s['count']:10d} {s['bad']:9d} "
                  f"{float(s['bad_fraction']):9.5f} {float(s['delta']):9.5f} "
                  + " ".join(str(e) for e in errs), flush=True)
    print(f"TOTAL addresses checked: {ncases}; configurations with a failing check: {fails}; "
          f"{time.time()-t0:.0f}s")
    return fails


if __name__ == '__main__':
    sys.exit(1 if main(int(sys.argv[1]) if len(sys.argv) > 1 else None) else 0)
