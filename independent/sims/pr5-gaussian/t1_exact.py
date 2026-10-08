"""T1: exact rational checks of the finite identities/inequalities in
notes/fast-gaussian-resampling.tex (PR 5 @ d3d370c).

Every check here is exact (Fraction) or rigorous (arb); no floats decide.
"""
import sys, random
from fractions import Fraction as Fr
from math import gcd, ceil
from common import *

setprec(256)
fails = []


def check(cond, msg):
    if not cond:
        fails.append(msg)
        print("FAIL:", msg)


# ---- (1) chirp identity  (sigma a^ - b)^2 = sigma theta a^2 + sigma (a^-b)^2 - theta b^2
rng = random.Random(1)
n1 = 0
for s in range(2, 40):
    for t in range(s + 1, 2 * s):
        if gcd(s, t) != 1:
            continue
        sig = Fr(t, s); th = sig - 1
        for _ in range(20):
            a = rng.randint(-50, 50); b = rng.randint(-50, 50)
            y = Fr(rng.randint(-10**6, 10**6), rng.randint(1, 10**6))
            lam = Fr(rng.randint(1, 10**4), rng.randint(1, 10**4))
            ah = a + y / sig
            check((sig * ah - b) ** 2 == sig * th * ah ** 2 + sig * (ah - b) ** 2 - th * b ** 2,
                  f"chirp identity s={s} t={t} a={a} b={b} y={y}")
            # exponent form of eq (chirp-split)
            lhs = lam * (sig * a + y - b) ** 2
            rhs = -lam * th * b ** 2 + lam * sig * th * (a + y / sig) ** 2 + lam * sig * (a - b + y / sig) ** 2
            check(lhs == rhs, f"chirp-split exponent s={s} t={t}")
            n1 += 2
print(flush=True); print(f"[1] chirp identity: {n1} exact instances checked")

# ---- (2) E formula: X_{l,h} equals the exponent read off N = C T D directly; X >= 0; |beta|<=1/2
n2 = 0
for (s, t) in admissible_pairs(24):
    sig = Fr(t, s)
    for l in range(s):
        assert abs(beta_of(s, t, l)) <= Fr(1, 2)
        for h in range(-2 * s - 2, 2 * s + 3):
            j = l + h
            direct = (sig * j - q_of(s, t, l)) ** 2 - beta_of(s, t, j % s) ** 2
            X = X_of(s, t, l, h)
            check(direct == X, f"X formula s={s} t={t} l={l} h={h}")
            check(X >= 0, f"X>=0 s={s} t={t} l={l} h={h}")
            check(q_of(s, t, j + s) == q_of(s, t, j) + t and beta_of(s, t, j + s) == beta_of(s, t, j),
                  f"periodicity s={s} t={t} j={j}")
            if h == 0:
                check(X == 0, "diag")
            n2 += 1
print(flush=True); print(f"[2] X formula / X>=0 / periodicity: {n2} exact instances")

# ---- (3) one-step identity and inequality of Lemma correction-powers
n3 = 0
minslack = None
for (s, t) in admissible_pairs(32):
    sig = Fr(t, s); th = sig - 1  # 0 < theta < 1
    Phi = lambda j: sig * (beta_of(s, t, j) ** 2 + Fr(1, 4)) / th
    for j in range(s):
        bj = beta_of(s, t, j)
        for h in range(-2 * s - 2, 2 * s + 3):
            if h == 0:
                continue
            c = sig * h * (sig * h + 2 * bj)
            check(c == (sig * h + bj) ** 2 - bj ** 2, "c def")
            y = bj + h * th
            w = q_of(s, t, j + h) - q_of(s, t, j) - h
            check(abs(y - w) <= Fr(1, 2), f"|y-w|<=1/2 s={s} t={t} j={j} h={h}")
            check(beta_of(s, t, j + h) == y - w, "beta_{j+h}=y-w")
            lhs = c - Phi(j + h) + Phi(j)
            check(lhs == sig * h * h + sig / th * w * (2 * y - w), f"step identity s={s} t={t} j={j} h={h}")
            check(lhs >= sig * h * h, f"step ineq s={s} t={t} j={j} h={h}")
            sl = lhs - sig * h * h
            minslack = sl if minslack is None else min(minslack, sl)
            # X_{j,h} = c + beta_j^2 - beta_{j+h}^2
            check(X_of(s, t, j, h) == c + bj ** 2 - beta_of(s, t, j + h) ** 2, "X = c + telescoping")
            n3 += 1
print(flush=True); print(f"[3] step identity + inequality (theta in (0,1), s<=32, |h|<=2s+2): {n3} exact instances; min slack {minslack}")

# ---- (4) path inequality X_path >= sigma sum h^2 - 1/(4 theta) - 1/2, exhaustive short paths
import itertools
n4 = 0; tight = None
steps = [h for h in range(-4, 5) if h]
for (s, t) in admissible_pairs(11):
    sig = Fr(t, s); th = sig - 1
    for j0 in range(s):
        for n in (1, 2, 3):
            for hs in itertools.product(steps, repeat=n):
                j = j0; X = 0
                for h in hs:
                    X += X_of(s, t, j, h); j += h
                rhs = sig * sum(h * h for h in hs) - 1 / (4 * th) - Fr(1, 2)
                check(X >= rhs, f"path ineq s={s} t={t} j0={j0} hs={hs}")
                g = X - rhs
                if tight is None or g < tight[0]:
                    tight = (g, s, t, j0, hs)
                n4 += 1
print(flush=True); print(f"[4] path inequality, all paths n<=3, |h_i|<=4, s<=11: {n4} exact instances; tightest slack {tight}")

# ---- (5) numeric constants used in the proofs (rigorous)
setprec(200)
pi = arb.pi(); log2e = 1 / arb(2).log()
k0 = pi * log2e
check(arb("4.531") < k0 and k0 < arb("4.534"), "4.531<kappa0<4.534")
check(lg2(arb("2.01")) < arb("1.01"), "log2 2.01 < 1.01")
# inner sum: sum_{h!=0} exp(-x h^2) < 2 e^{-x}(1+2e^{-3x}) < 2.01 e^{-x} for x > 4 pi  (check at x = 4 pi, worst case)
x = 4 * pi
S = sum(2 * (-x * h * h).exp() for h in range(1, 6)) + arb(0, (2 * (-x * 36).exp()).upper())
check(S < 2 * (-x).exp() * (1 + 2 * (-3 * x).exp()), "inner sum < 2e^{-x}(1+2e^{-3x})")
check(2 * (1 + 2 * (-3 * x).exp()) < arb("2.01"), "2(1+2e^{-3x})<2.01")
# corollary: kappa0 a^2 sigma - 1.01 >= 4 a^2  for a>=2, sigma>1 : (kappa0-4) a^2 >= 1.01 at a=2
check((k0 - 4) * 4 > arb("1.01"), "(k0-4)*4 > 1.01")
# 4.534 (1/(4 th) + 1/2) <= 4/th  for 0<th<1  <=> 4.534/2 <= (4 - 4.534/4)/th ; worst th -> 1
check(Fr(4534, 1000) * (Fr(1, 4) + Fr(1, 2)) <= 4, "4.534(1/4+1/2)<=4 (theta=1 limit)")
# (2.01 e^{-pi/2}) < 0.42 and < 2^{-1}: ||E|| bound at alpha^2 theta = 1
check(arb("2.01") * (-pi / 2).exp() < arb("0.42"), "2.01 e^{-pi/2} < 0.42")
# 2.01 e^{-pi x/2} < 2^{-x} for x >= 1 : log(2.01) < x (pi/2 - ln2), worst at x=1
check(arb("2.01").log() < (pi / 2 - arb(2).log()), "2.01e^{-pi x/2}<2^{-x} at x=1")

# Gamma / P conditions (S' map): pi*theta*(sqrt p + 1)^2 * log2 e <= ceil(1.4 p) for theta<=1/4, p>100;
# and P=3p >= p + Gamma + ceil(log2(F L_A)) + 11 with F=1, L_A = 3m+3, m=ceil(sqrt p)*alpha, alpha^2<p
bad_S = []; bad_E = []; bad_Ef = []
for p in list(range(101, 1200)) + [2000, 5000, 10**4, 10**5, 10**6]:
    G = -(-14 * p // 10)
    sq = ceil_sqrt(p)
    # exact need: max over b<m of pi lam theta b^2 = pi theta (m-1)^2/(sigma^2 alpha^2) <= pi theta sq^2 (crude, sigma>1)
    e = pi / 4 * sq * sq * log2e
    if not (e < G):
        bad_S.append((p, 'Gamma'))
    amax = isqrt(p - 1)  # largest integer alpha with alpha^2 < p
    for al in {2, amax}:
        m = sq * al; LA = 3 * m + 3
        if not (p + G + (LA - 1).bit_length() + 11 <= 3 * p):
            bad_S.append((p, al, 'P'))
        # E map
        mE = 1
        while (2 * al * mE) ** 2 < p:
            mE += 1
        LAE = 3 * mE + 1; LBE = 2 * mE + 2
        GE = 29 * p
        eE = pi / 4 * al * al * (2 * mE + 1) ** 2 * log2e
        if not (eE < GE):
            bad_E.append((p, al, 'Gamma'))
        F = (pi * al * al / 4).exp()
        need = lg2(F * LAE)  # ceil(log2(F L_A))
        Pneed = p + GE + int(need.upper().ceil().unique_fmpz()) + 11
        if Pneed > 34 * p:
            bad_E.append((p, al, 'P'))
        # alternative F' = 2^{ceil(1.14 a^2)}
        Fp_bits = -(-114 * al * al // 100)
        if p + GE + Fp_bits + (LAE - 1).bit_length() + 1 + 11 > 34 * p:
            bad_Ef.append((p, al))
check(not bad_S, f"S' Gamma/P conditions {bad_S[:5]}")
check(not bad_E, f"E Gamma/P conditions {bad_E[:5]}")
check(not bad_Ef, f"E P condition with F'=2^ceil(1.14a^2) {bad_Ef[:5]}")
print("[5] constants / Gamma / P conditions checked for p in 101..1199 and 2e3,5e3,1e4,1e5,1e6")

# ---- (6) the stated input-error bound for f_j in the E map: |f~ - f| <= 2^{4-P} F with F = e^{pi a^2/4}.
# Lemma 2.14 is quoted as giving z~ ~ 2^{-K} e^{pi a^2 beta^2}, K=ceil(1.14 a^2), with error <= 2^{1-P};
# the shift multiplies that error by 2^K. Worst allowed error after shift & product with |u|=1 is
# ~2^{K+1-P} (+ rounding 2^{-P}/sqrt2 per component). Find where it exceeds 2^{4-P} e^{pi a^2/4}.
first = None
for al in range(2, 200):
    K = -(-114 * al * al // 100)
    worst = arb(2) ** (K + 1) + 1  # in units 2^{-P}: shifted approx error + rounding (<=1)
    claim = 16 * (pi * al * al / 4).exp()
    if worst > claim:
        first = al; break
print(flush=True); print(f"[6] literal f-error bound 2^(4-P) e^(pi a^2/4) can be exceeded by an allowed approximation once alpha >= {first}"
      f" (needs p > alpha^2 = {first*first if first else None})")

print("TOTAL FAILS:", len(fails))
sys.exit(1 if fails else 0)
