"""Exact arithmetic for PR 7 and PR 8 headline constants (Fractions only)."""
from fractions import Fraction as Q
from math import comb


def log_upper(m, bound):
    """exact check log(m) < bound via exp(bound) > m using a lower Taylor bound
    of exp on the rational bound (all terms positive)."""
    s, t = Q(0), Q(1)
    for k in range(1, 80):
        s += t
        t = t * bound / k
    return s > m


ok = True
# ---- PR 7 bit side
h = 28; v = comb(h, 5); m = h ** 3; N = v ** 3; R = 10857762 + 983178
W = 2 * v * v * (v + R); L = 3 * v * v * comb(h, 2) * (h - 2); s = W * m - N + 2 * L
eta = Q(W * m - s, W * m)
c = [W == 230640858616896000, s == 5063027748645128371200, eta == Q(39, 520019360),
     eta > Q(3, 400000000) * Q(9997, 1000), log_upper(m, Q(9997, 1000)), N - 2 * L > 0]
print('PR7 bit  W', W, 's', s, 'eta', eta, 'checks', c); ok &= all(c)
# ---- PR 7 complex side
vc = comb(h, 3); Rc = 61022 + 32816
Wc = 2 * vc * vc * (vc + Rc + h + 1); Lc = 3 * vc * vc * h * (h + 1); sc = Wc * m - 2 * vc ** 3 + 2 * Lc
ec = Q(Wc * m - sc, Wc * m)
gates = 3 * vc * vc * (4 * (61022 + vc) + 4 * vc + 4)
c = [Wc == 2085111546336, ec == Q(5, 12693352), ec > Q(39, 10 ** 9) * 10, log_upper(m, Q(10)), gates < 12 * Wc]
print('PR7 cplx W', Wc, 'eta', ec, 'checks', c); ok &= all(c)
# ---- PR 8
n = 25; h8 = 26; v8 = comb(n, 3); m8 = h8 ** 3; N8 = v8 ** 3; R8 = 212737 + 2300 + 36620 + 6900
W8 = 2 * N8 + 3 * v8 * v8 * (R8 + n + 1); L8 = 3 * v8 * v8 * (n + 1) * h8; s8 = W8 * m8 - 2 * N8 + 2 * L8
e8 = Q(W8 * m8 - s8, W8 * m8)
c = [R8 == 258557, W8 == 4128046210000, L8 == 10728120000, s8 == 72554537309200000, e8 == Q(68, 1714426753),
     log_upper(m8, Q(9775, 1000)), e8 > Q(4, 10 ** 9) * Q(9775, 1000)]
print('PR8      W', W8, 's', s8, 'eta', e8, 'checks', c); ok &= all(c)
I8 = 3 * v8 * v8; E0 = 64 * (W8 + m8 + 1) ** 3
c = [32 * I8 * (R8 + v8 + n + 1) + 4 * s8 + 4 * W8 + 4 < E0, 2 <= s8 < m8 ** 5]
print('PR8 guard inequalities', c); ok &= all(c)
tau = 1 - Q(296, 10 ** 11); sigma = 1 - Q(4, 10 ** 9); eps = Q(1999, 10000); cc = 1; beta = Q(1, 1000)
zeta = Q(1, 10000); delta = Q(1, 10 ** 6); lam = 1 - Q(2959, 10 ** 12); lamp = 1 - Q(2958, 10 ** 12)
kappa = Q(59, 10 ** 11); C1 = Q(49961, 10000)
chi = tau + (1 - beta) * max(sigma - tau, 0); leaf = sigma + beta * (1 - sigma)
g = [1 - eps * (1 + cc), eps * cc * (1 - tau), eps * (1 - lamp), (1 - tau) * (1 - eps),
     Q(1, 4) - delta - 5 * eps / 4, 1 - delta - eps, eps]
c = [C1 == 5 - 4 * beta + zeta, eps * C1 < 1, eps * (1 + cc) < 1, max(tau, sigma, chi) < lam < lamp < 1,
     max(leaf, 1 - cc, 0) < lamp, min(g) == Q(2956521, 5 * 10 ** 15), min(g) > kappa]
print('PR8 layer/assembly (the seven margins as written in the note)', c, 'min', min(g)); ok &= all(c)
# ---- PR 7 layer conditions (compact-control form; assembly margins themselves use PR 5's fast-Gaussian
#      bookkeeping, checked in round 1, so only g_3 is recomputed here)
tau7 = 1 - Q(3, 400000000); sig7 = 1 - Q(39, 10 ** 9); e7 = Q(4999, 10000); c7 = Q(9999, 10000); b7 = Q(19, 25)
l7 = 1 - Q(749, 10 ** 11); lp7 = 1 - Q(748, 10 ** 11); z7 = Q(1, 10 ** 4)
chi7 = tau7 + (1 - b7) * max(sig7 - tau7, 0); leaf7 = sig7 + b7 * (1 - sig7)
c = [Q(19601, 10000) == 5 - 4 * b7 + z7, e7 * Q(19601, 10000) < 1, e7 * (1 + c7) < 1,
     max(tau7, sig7, chi7) < l7 < lp7 < 1, max(leaf7, 1 - c7, 0) < lp7,
     e7 * (1 - lp7) == Q(934813, 250000000000000), e7 * (1 - lp7) - Q(373, 10 ** 11) == Q(2313, 250000000000000)]
print('PR7 layer conditions and g_3', c); ok &= all(c)
print('ARITH', 'PASS' if ok else 'FAIL')
