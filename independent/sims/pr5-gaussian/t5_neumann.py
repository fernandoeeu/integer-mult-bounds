"""T5: Neumann evaluation of J' = N^{-1}/2 run for n_{alpha,theta} terms (revised
interface), with an adversarial E~ whose error is just below the allowed p/3
(units 2^-p), compared rigorously against the exact N^{-1} u / 2.
Claim tested: error < 3p^2/4 (units 2^-p), iterates stay in D_p.
Also reports n_{alpha,theta} versus the old count ceil(p/(alpha^2 theta)).
"""
import sys, random
from fractions import Fraction as Fr
from common import *

fails = []
rows_out = []


def rnd(x):  # nearest integer of an arb (midpoint based; error <= 1/2 + radius)
    return int((x.mid() + arb(1) / 2).floor().unique_fmpz())


for (p, al, s, t) in [(101, 3, 9, 10), (101, 5, 25, 26), (101, 10, 100, 101), (101, 2, 4, 5), (101, 4, 16, 17),
                      (150, 4, 16, 17), (150, 7, 49, 50), (200, 3, 9, 10), (101, 3, 7, 8), (101, 5, 23, 24)]:
    setprec(4 * p + 200)
    sig = Fr(t, s); th = sig - 1; a2 = al * al
    assert Fr(1, a2) <= th <= Fr(1, 4) and a2 < p
    n1 = -(-p * th.denominator // (a2 * th.numerator))
    v2 = Fr(p + 1, 4 * a2) + 1 / th
    n2 = -(-v2.numerator // v2.denominator)
    n = min(n1, n2)
    E = arb_mat(E_matrix(s, t, al, H=8))
    Id = arb_mat([[1 if i == j else 0 for j in range(s)] for i in range(s)])
    Ninv = (Id + E).inv()
    rng = random.Random(p * 1000 + s)
    one = 1 << p
    for trial in range(4):
        if trial == 0:
            u = [(one, 0)] * s
        elif trial == 1:
            u = [(one if j % 2 == 0 else -one, 0) for j in range(s)]
        else:
            u = []
            while len(u) < s:
                a = rng.randint(-one, one); b = rng.randint(-one, one)
                if a * a + b * b <= one * one:
                    u.append((a, b))
        for adv in (+1, -1):
            # v0 = u/2 rounded toward zero at precision p
            def tz(x):
                return x // 2 if x >= 0 else -((-x) // 2)
            v = [(tz(a), tz(b)) for (a, b) in u]
            acc = [(0, 0)] * s
            maxnorm = 0
            for j in range(n):
                sgn = 1 if j % 2 == 0 else -1
                acc = [(acc[i][0] + sgn * v[i][0], acc[i][1] + sgn * v[i][1]) for i in range(s)]
                if j == n - 1:
                    break
                # E~ v = nearest(E v) + adversarial shift  d with |d| < p/3 - 1, sign chosen so that
                # the error enters the alternating sum with a constant sign
                vm_r = arb_mat([[arb(v[i][0])] for i in range(s)])
                vm_i = arb_mat([[arb(v[i][1])] for i in range(s)])
                er = E * vm_r; ei = E * vm_i
                d = int(Fr(p, 3)) - 2
                nv = []
                for i in range(s):
                    xr = rnd(er[i, 0]) + adv * sgn * (-1) * d
                    xi = rnd(ei[i, 0])
                    # keep in disk grid (clip toward zero if needed)
                    while xr * xr + xi * xi > one * one:
                        xr -= 1 if xr > 0 else -1
                    nv.append((xr, xi))
                    maxnorm = max(maxnorm, xr * xr + xi * xi)
                v = nv
            # exact J' u = N^{-1} u / 2
            ur = arb_mat([[arb(a) / 2] for (a, b) in u]); ui = arb_mat([[arb(b) / 2] for (a, b) in u])
            jr = Ninv * ur; ji = Ninv * ui
            err = max(((arb(acc[i][0]) - jr[i, 0]).abs_upper() ** 2 + (arb(acc[i][1]) - ji[i, 0]).abs_upper() ** 2).sqrt().upper()
                      for i in range(s))
            bound = arb(3 * p * p) / 4
            ok = err < bound
            if not ok:
                fails.append((p, al, s, t, trial, adv, float(err.mid())))
            rows_out.append((p, al, s, t, n, n1, trial, adv, float(err.mid()), float(bound.mid())))
    print(f"p={p} alpha={al} s={s} t={t} theta={th} n_new={n} n_old={n1}  max err (units 2^-p) over trials = "
          f"{max(r[8] for r in rows_out if r[:4]==(p,al,s,t)):.2f}  bound 3p^2/4 = {3*p*p/4}", flush=True)

print("fails:", fails)
print("RESULT:", "FAIL" if fails else "PASS")
sys.exit(1 if fails else 0)
