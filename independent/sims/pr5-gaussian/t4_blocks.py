"""T4: independent implementation of Lemma chirped-gaussian (PR 5,
notes/fast-gaussian-resampling.tex) for the maps S' and E, exactly as written:
chirp split, precision-P factor approximations (error <= 2^{1-P}; modes:
nearest, worst-case up, worst-case down, random +-), rounding to precision P,
packing into integers with slots of 2P + ceil(log2(F L_A)) + 8 bits, one big
integer product per sign/component, output factor 2^{-Gamma} e^{pi lam theta b^2},
shift by Gamma, round to precision p.

Every stated intermediate bound is checked against a rigorous Arb reference:
  (i)   |f~ - f| <= 2^{4-P} F                         (E map inputs)
  (ii)  |g~ - g| <= 2^{5-P} F
  (iii) |c~ - c| <= 2^{7-P} F L_A,   |c| <= F L_A
  (iv)  slots never overflow (packed product == direct correlation)
  (v)   |pre-rounding block value - F_b| <= 2^{Gamma+9-P} F L_A <= 2^{-p-2}
  (vi)  window coverage claims
  (vii) final: S' error < 3*2^{-p} (and < 16p 2^{-p}); E error < 5*2^{-p} (and < (p/3)2^{-p});
        outputs in the disk grid D_p.
usage: t4_blocks.py p alpha s t [input_modes] [approx_modes]
"""
import sys, random
from fractions import Fraction as Fr
from common import *

pi = None
LOG = []
import os
DEBUG = os.environ.get("DBG") == "1"


def nearest_shift(n, k):
    """nearest integer to n / 2^k (k >= 0)."""
    if k <= 0:
        return n << (-k)
    return (n + (1 << (k - 1))) >> k


def approx_int(x, P, mode, rng, clamp01=True):
    """Integer r with |x 2^P - r| <= 2 (i.e. error <= 2^{1-P}), certified."""
    y = x * (arb(2) ** P)
    lo = int(y.lower().floor().unique_fmpz())
    hi = int(y.upper().ceil().unique_fmpz())
    assert hi - lo <= 1, "insufficient working precision"
    if mode == 'near':
        cands = [int((y.mid() + arb(1) / 2).floor().unique_fmpz())]
    elif mode == 'up':
        cands = [hi + 1, hi]
    elif mode == 'down':
        cands = [lo - 1, lo]
    else:
        c = rng.choice([lo - 1, lo, hi, hi + 1])
        cands = [c, lo, hi]
    for r in cands:
        if clamp01:
            r = max(0, min(r, 1 << P))
        if (y - r).abs_upper() <= 2:
            break
    else:
        raise AssertionError("no admissible approximation")
    return r


def correlate_packed(g, Kd, LA, LB, W):
    """c_b = sum_a g_a K_{a-b}, b in [0,LB). g: list of (re,im) ints; Kd: dict r->nonneg int.
    Kronecker packing with slots of W bits, nonneg/neg split of g components."""
    Kp = [Kd[r] for r in range(-(LB - 1), LA)]          # K'_i = K_{i-(LB-1)}
    assert all(k >= 0 for k in Kp)
    nK = len(Kp)
    PK = 0
    for i in reversed(range(nK)):
        PK = (PK << W) | Kp[i]
    res = []
    maxslot = 0
    for comp in (0, 1):
        parts = []
        for sign in (1, -1):
            G = [max(0, sign * g[LA - 1 - i][comp]) for i in range(LA)]  # reversed g
            PG = 0
            for i in reversed(range(LA)):
                PG = (PG << W) | G[i]
            prod = PG * PK
            mask = (1 << W) - 1
            vals = []
            for b in range(LB):
                idx = LA + LB - 2 - b
                v = (prod >> (W * idx)) & mask
                vals.append(v)
            # independent direct computation to detect overflow / mis-indexing
            for b in range(LB):
                dv = sum(G[LA - 1 - a] * Kd[a - b] for a in range(LA))
                maxslot = max(maxslot, dv.bit_length())
                if dv != vals[b]:
                    raise AssertionError(f"slot overflow / packing mismatch at b={b}: {dv.bit_length()} bits vs W={W}")
            parts.append(vals)
        res.append([parts[0][b] - parts[1][b] for b in range(LB)])
    return [(res[0][b], res[1][b]) for b in range(LB)], maxslot


def rand_disk(p, rng):
    while True:
        a = rng.randint(-(1 << p), 1 << p); b = rng.randint(-(1 << p), 1 << p)
        if a * a + b * b <= 1 << (2 * p):
            return (a, b)


def make_inputs(s, p, mode, rng):
    one = 1 << p
    if mode == 'ones':
        return [(one, 0) for _ in range(s)]
    if mode == 'neg':
        return [(-one, 0) for _ in range(s)]
    if mode == 'alt':
        return [[(one, 0), (0, one), (-one, 0), (0, -one)][j % 4] for j in range(s)]
    if mode == 'rand':
        return [rand_disk(p, rng) for _ in range(s)]
    if mode == 'rim':  # near the disk boundary, random phase
        out = []
        for _ in range(s):
            a = rng.randint(-(1 << p), 1 << p)
            b2 = (1 << (2 * p)) - a * a
            from math import isqrt
            b = isqrt(b2) * rng.choice([1, -1])
            out.append((a, b))
        return out
    raise ValueError(mode)


def cplx_arb(z, scale):
    return (arb(z[0]) / arb(2) ** scale, arb(z[1]) / arb(2) ** scale)


def absc(re, im):
    """Rigorous enclosure of |re + i im| for real balls re, im."""
    lo = (re.abs_lower() ** 2 + im.abs_lower() ** 2).sqrt()
    hi = (re.abs_upper() ** 2 + im.abs_upper() ** 2).sqrt()
    return lo.union(hi)


def run(p, al, s, t, in_modes, ap_modes, seed=0, maps=('S', 'E')):
    global pi
    sig = Fr(t, s); th = sig - 1
    a2 = al * al
    assert p > 100 and 2 <= al and a2 < p and 2 <= s < t and Fr(1, a2) <= th <= Fr(1, 4)
    from math import gcd
    assert gcd(s, t) == 1
    rng = random.Random(seed)
    out = dict(params=(p, al, s, t), S=dict(), E=dict(), checks=0, fails=[])

    def chk(cond, msg):
        out['checks'] += 1
        if not cond:
            out['fails'].append(msg)

    if 'S' in maps:
        # ======================= S' map =======================
        P = 3 * p; G = -(-14 * p // 10)
        setprec(P + 96); pi = arb.pi()
        m = ceil_sqrt(p) * al
        lam = Fr(s * s, t * t * a2)
        LA = 3 * m + 3
        F = 1
        W = 2 * P + (F * LA - 1).bit_length() + 8   # ceil(log2(F L_A)) = bit_length(L_A - 1) for L_A>1
        inv2a = arb(1) / (2 * al)
        # per-block exact factors (arb), shared by all approximation modes
        blocks = []
        for k0 in range(0, t, m):
            LB = min(m, t - k0)
            j0 = (k0 * s) // t - m
            y = sig * j0 - k0
            # coverage: every j with |j - k/sigma| < m lies in [j0, j0+LA)
            for b in range(LB):
                k = k0 + b
                jlo = Fr(k * s, t) - m; jhi = Fr(k * s, t) + m
                # integers strictly inside (jlo, jhi)
                first = jlo.__floor__() + 1; last = (jhi.__ceil__()) - 1
                chk(j0 <= first and last <= j0 + LA - 1, f"S' coverage k={k}")
            gf = [(-pi * A(lam * sig * th * (a + y / sig) ** 2)).exp() for a in range(LA)]
            Kf = {r: (-pi * A(lam * sig * (r + y / sig) ** 2)).exp() for r in range(-(LB - 1), LA)}
            of = [(pi * A(lam * th * b * b)).exp() / arb(2) ** G for b in range(LB)]
            for b in range(LB):
                chk(of[b] <= 1, f"S' e^(pi lam th b^2) <= 2^Gamma b={b}")
            wdir = [[(-pi * A(lam * (sig * a + y - b) ** 2)).exp() for a in range(LA)] for b in range(LB)]
            blocks.append((k0, LB, j0, y, gf, Kf, of, wdir))
        Wref = m + 6 * al
        wfull = []
        for k in range(t):
            c = Fr(k * s, t); jc = int(c)
            wfull.append([(j % s, (-pi * A((j - c) ** 2) / a2).exp()) for j in range(jc - Wref - 1, jc + Wref + 2)])
        for im in in_modes:
            u = make_inputs(s, p, im, rng)
            ua = [cplx_arb(z, p) for z in u]
            # exact (S'u)_k with a wide window + tail
            tail = 4 * (-pi * arb(Wref) ** 2 / a2).exp() / (2 * al)
            exact = []
            for k in range(t):
                re = arb(0); imv = arb(0)
                for (jm, w) in wfull[k]:
                    re += w * ua[jm][0]; imv += w * ua[jm][1]
                exact.append((re / (2 * al) + arb(0, tail.upper()), imv / (2 * al) + arb(0, tail.upper())))
            # exact per-block quantities (independent of approximation mode)
            bex = []
            for (k0, LB, j0, y, gf, Kf, of, wdir) in blocks:
                gex = [(ua[(j0 + a) % s][0] * gf[a], ua[(j0 + a) % s][1] * gf[a]) for a in range(LA)]
                cexs = [(sum((gex[a][0] * Kf[a - b] for a in range(LA)), arb(0)),
                         sum((gex[a][1] * Kf[a - b] for a in range(LA)), arb(0))) for b in range(LB)]
                Fbs = [(sum((wdir[b][a] * ua[(j0 + a) % s][0] for a in range(LA)), arb(0)),
                        sum((wdir[b][a] * ua[(j0 + a) % s][1] for a in range(LA)), arb(0))) for b in range(LB)]
                bex.append((gex, cexs, Fbs))
            for am in ap_modes:
                worst = dict(final=arb(0), pre=arb(0), g=arb(0), c=arb(0), slot=0, normout=arb(0), finalB=arb(0))
                inv_int = approx_int(inv2a, P, am, rng)
                for bi_, (k0, LB, j0, y, gf, Kf, of, wdir) in enumerate(blocks):
                    gex, cexs, Fbs = bex[bi_]
                    gi = [approx_int(x, P, am, rng) for x in gf]
                    Ki = {r: approx_int(x, P, am, rng) for r, x in Kf.items()}
                    oi = [approx_int(x, P, am, rng) for x in of]
                    fa = [u[(j0 + a) % s] for a in range(LA)]
                    gt = [(nearest_shift((z[0] << (P - p)) * gi[a], P), nearest_shift((z[1] << (P - p)) * gi[a], P))
                          for a, z in enumerate(fa)]
                    # (ii) |g~ - g| <= 2^{5-P} F
                    for a in range(LA):
                        ex = gex[a]
                        e = absc(arb(gt[a][0]) / arb(2) ** P - ex[0], arb(gt[a][1]) / arb(2) ** P - ex[1])
                        worst['g'] = arb(max(worst['g'].upper(), (e * arb(2) ** P).upper()))
                        chk(e <= arb(2) ** (5 - P) * F, f"S' g err a={a}")
                    ct, ms = correlate_packed(gt, Ki, LA, LB, W)
                    worst['slot'] = max(worst['slot'], ms)
                    chk(ms < W, "S' slot")
                    for b in range(LB):
                        k = k0 + b
                        cex = cexs[b]
                        chk(absc(*cex) <= F * LA, "S' |c|<=F L_A")
                        e = absc(arb(ct[b][0]) / arb(2) ** (2 * P) - cex[0], arb(ct[b][1]) / arb(2) ** (2 * P) - cex[1])
                        worst['c'] = arb(max(worst['c'].upper(), (e * arb(2) ** P / LA).upper()))
                        chk(e <= arb(2) ** (7 - P) * F * LA, f"S' c err b={b}")
                        # pre-rounding value  c~ * o~ * 2^Gamma, scaled 2^{-3P}
                        vr = ct[b][0] * oi[b] << G; vi = ct[b][1] * oi[b] << G
                        # exact block sum F_b = sum_a e^{-pi lam (sig a + y - b)^2} f_a
                        Fb = Fbs[b]
                        e = absc(arb(vr) / arb(2) ** (3 * P) - Fb[0], arb(vi) / arb(2) ** (3 * P) - Fb[1])
                        worst['pre'] = arb(max(worst['pre'].upper(), (e * arb(2) ** p).upper()))
                        chk(e <= arb(2) ** (G + 9 - P) * F * LA, "S' pre <= 2^{G+9-P} F L_A")
                        chk(e <= arb(2) ** (-p - 2), "S' pre <= 2^{-p-2}")
                        # round to precision p, then multiply by (2a)^{-1} at precision P, round to p (variant A)
                        zr = nearest_shift(vr, 3 * P - p); zi = nearest_shift(vi, 3 * P - p)
                        fr_ = nearest_shift(zr * inv_int, P); fi_ = nearest_shift(zi * inv_int, P)
                        # variant B: single rounding
                        br = nearest_shift(vr * inv_int, 4 * P - p); bi = nearest_shift(vi * inv_int, 4 * P - p)
                        for (xr, xi, key) in ((fr_, fi_, 'final'), (br, bi, 'finalB')):
                            e = absc(arb(xr) / arb(2) ** p - exact[k][0], arb(xi) / arb(2) ** p - exact[k][1]) * arb(2) ** p
                            if DEBUG and k < 2: print("DBG", k, key, xr, xi, [str(z)[:60] for z in exact[k]], e)
                            worst[key] = arb(max(worst[key].upper(), e.upper()))
                            chk(e < 3, f"S' final error <3 ({key}) k={k}")
                            chk(e < 16 * p, "S' final < 16p")
                            chk(xr * xr + xi * xi <= 1 << (2 * p), "S' output in D_p")
                            nrm = absc(arb(xr), arb(xi)) / arb(2) ** p
                            worst['normout'] = arb(max(worst['normout'].upper(), nrm.upper()))
                out['S'][(im, am)] = {k: float(v.mid()) if hasattr(v, 'mid') else v for k, v in worst.items()}

    if 'E' in maps:
        # ======================= E map =======================
        P = 34 * p; G = 29 * p
        setprec(P + 96); pi = arb.pi()
        mE = 1
        while (2 * al * mE) ** 2 < p:
            mE += 1
        m = mE
        lam = Fr(a2)
        LA = 3 * m + 1; LBf = 2 * m + 2
        Farb = (pi * a2 / 4).exp()
        logFL = lg2(Farb * LA)
        W = 2 * P + int(logFL.upper().ceil().unique_fmpz()) + 8
        KD = -(-114 * a2 // 100)
        zf = [(pi * a2 * A(beta_of(s, t, j) ** 2)).exp() / arb(2) ** KD for j in range(s)]
        blocks = []
        for l0 in range(0, s, m):
            j0 = l0 - m
            ql0 = q_of(s, t, l0)
            y = sig * j0 - ql0
            ls = list(range(l0, min(l0 + m, s)))
            for l in ls:
                b = q_of(s, t, l) - ql0
                chk(0 <= b < LBf, f"E output index in range l={l}")
                for h in range(-m, m + 1):
                    chk(j0 <= l + h <= j0 + LA - 1, f"E coverage l={l} h={h}")
            gf = [(-pi * A(lam * sig * th * (a + y / sig) ** 2)).exp() for a in range(LA)]
            Kf = {r: (-pi * A(lam * sig * (r + y / sig) ** 2)).exp() for r in range(-(LBf - 1), LA)}
            of = [(pi * A(lam * th * b * b)).exp() / arb(2) ** G for b in range(LBf)]
            for b in range(LBf):
                chk(of[b] <= 1, f"E e^(pi lam th b^2) <= 2^Gamma b={b}")
            blocks.append((l0, ls, j0, ql0, y, gf, Kf, of))
        for im in in_modes:
            u = make_inputs(s, p, im, rng)
            setprec(P + 96)
            ua = [cplx_arb(z, p) for z in u]
            fex = [(zf[j] * arb(2) ** KD * ua[j][0], zf[j] * arb(2) ** KD * ua[j][1]) for j in range(s)]
            # exact (E u)_l with wide window
            H = m + 8
            tail = 4 * (-pi * a2 * H * (H + 1)).exp()
            exact = []
            for l in range(s):
                re = arb(0); imv = arb(0)
                for h in range(-H, H + 1):
                    if h == 0:
                        continue
                    w = (-pi * a2 * A(X_of(s, t, l, h))).exp()
                    re += w * ua[(l + h) % s][0]; imv += w * ua[(l + h) % s][1]
                exact.append((re + arb(0, tail.upper()), imv + arb(0, tail.upper())))
            for am in ap_modes:
                worst = dict(final=arb(0), pre=arb(0), f_over_claim=arb(0), g=arb(0), c=arb(0), slot=0, normout=arb(0))
                zi_ = [approx_int(x, P, am, rng) for x in zf]
                ft = []
                for j in range(s):
                    # shift by KD then product with u_j, round to precision P
                    vr = nearest_shift((u[j][0] << (P - p)) * (zi_[j] << KD), P)
                    vi = nearest_shift((u[j][1] << (P - p)) * (zi_[j] << KD), P)
                    ft.append((vr, vi))
                    e = absc(arb(vr) / arb(2) ** P - fex[j][0], arb(vi) / arb(2) ** P - fex[j][1])
                    ratio = e / (arb(2) ** (4 - P) * Farb)
                    worst['f_over_claim'] = arb(max(worst['f_over_claim'].upper(), ratio.upper()))
                    chk(e <= arb(2) ** (4 - P) * Farb, f"E f err <= 2^(4-P) e^(pi a^2/4) j={j}")
                    chk(e <= arb(2) ** (4 - P + KD), f"E f err <= 2^(4-P) 2^K (repaired F) j={j}")
                for (l0, ls, j0, ql0, y, gf, Kf, of) in blocks:
                    gi = [approx_int(x, P, am, rng) for x in gf]
                    Ki = {r: approx_int(x, P, am, rng) for r, x in Kf.items()}
                    oi = [approx_int(x, P, am, rng) for x in of]
                    fa = [ft[(j0 + a) % s] for a in range(LA)]
                    gt = [(nearest_shift(z[0] * gi[a], P), nearest_shift(z[1] * gi[a], P)) for a, z in enumerate(fa)]
                    gex = []
                    for a in range(LA):
                        fe = fex[(j0 + a) % s]
                        ex = (fe[0] * gf[a], fe[1] * gf[a]); gex.append(ex)
                        e = absc(arb(gt[a][0]) / arb(2) ** P - ex[0], arb(gt[a][1]) / arb(2) ** P - ex[1])
                        worst['g'] = arb(max(worst['g'].upper(), (e * arb(2) ** P / Farb).upper()))
                        chk(e <= arb(2) ** (5 - P) * Farb, f"E g err a={a}")
                    ct, ms = correlate_packed(gt, Ki, LA, LBf, W)
                    worst['slot'] = max(worst['slot'], ms)
                    chk(ms < W, "E slot")
                    for l in ls:
                        b = q_of(s, t, l) - ql0
                        cex = (sum((gex[a][0] * Kf[a - b] for a in range(LA)), arb(0)),
                               sum((gex[a][1] * Kf[a - b] for a in range(LA)), arb(0)))
                        chk(absc(*cex) <= Farb * LA, "E |c| <= F L_A")
                        e = absc(arb(ct[b][0]) / arb(2) ** (2 * P) - cex[0], arb(ct[b][1]) / arb(2) ** (2 * P) - cex[1])
                        worst['c'] = arb(max(worst['c'].upper(), (e * arb(2) ** P / (LA * Farb)).upper()))
                        chk(e <= arb(2) ** (7 - P) * Farb * LA, "E c err")
                        vr = ct[b][0] * oi[b] << G; vi = ct[b][1] * oi[b] << G
                        Fb = (sum(((-pi * A(lam * (sig * a + y - b) ** 2)).exp() * fex[(j0 + a) % s][0] for a in range(LA)), arb(0)),
                              sum(((-pi * A(lam * (sig * a + y - b) ** 2)).exp() * fex[(j0 + a) % s][1] for a in range(LA)), arb(0)))
                        e = absc(arb(vr) / arb(2) ** (3 * P) - Fb[0], arb(vi) / arb(2) ** (3 * P) - Fb[1])
                        worst['pre'] = arb(max(worst['pre'].upper(), (e * arb(2) ** p).upper()))
                        chk(e <= arb(2) ** (G + 9 - P) * Farb * LA, "E pre <= 2^{G+9-P} F L_A")
                        chk(e <= arb(2) ** (-p - 2), "E pre <= 2^{-p-2}")
                        zr = nearest_shift(vr, 3 * P - p) - u[l][0]
                        zi = nearest_shift(vi, 3 * P - p) - u[l][1]
                        e = absc(arb(zr) / arb(2) ** p - exact[l][0], arb(zi) / arb(2) ** p - exact[l][1]) * arb(2) ** p
                        worst['final'] = arb(max(worst['final'].upper(), e.upper()))
                        chk(e < 5, f"E final error < 5 l={l}")
                        chk(e < arb(p) / 3, "E final < p/3")
                        chk(zr * zr + zi * zi <= 1 << (2 * p), "E output in D_p")
                        nrm = absc(arb(zr), arb(zi)) / arb(2) ** p
                        worst['normout'] = arb(max(worst['normout'].upper(), nrm.upper()))
                out['E'][(im, am)] = {k: float(v.mid()) if hasattr(v, 'mid') else v for k, v in worst.items()}
    return out


if __name__ == '__main__':
    p, al, s, t = map(int, sys.argv[1:5])
    ims = sys.argv[5].split(',') if len(sys.argv) > 5 else ['ones', 'rand', 'rim', 'alt']
    ams = sys.argv[6].split(',') if len(sys.argv) > 6 else ['near', 'up', 'down', 'rand']
    import time
    t0 = time.time()
    maps = sys.argv[7].split(',') if len(sys.argv) > 7 else ['S', 'E']
    r = run(p, al, s, t, ims, ams, maps=maps)
    print(f"params p={p} alpha={al} s={s} t={t} theta={Fr(t-s,s)} checks={r['checks']} fails={len(r['fails'])} time={time.time()-t0:.1f}s")
    for key in ('S', 'E'):
        for k, v in r[key].items():
            print(f"  {key} {k}: " + ", ".join(f"{a}={b:.4g}" if isinstance(b, float) else f"{a}={b}" for a, b in v.items()))
    if r['fails']:
        from collections import Counter
        print("  FAIL kinds:", Counter(f.split(' j=')[0].split(' a=')[0].split(' k=')[0].split(' l=')[0].split(' b=')[0] for f in r['fails']))
        print("  first fails:", r['fails'][:5])
    print("RESULT:", "FAIL" if r['fails'] else "PASS")
    sys.exit(1 if r['fails'] else 0)
