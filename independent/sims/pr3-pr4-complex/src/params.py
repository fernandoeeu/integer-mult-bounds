"""Exact rank accounting and recurrence-exponent checks from the counts
obtained by the independent constructions (Fractions only)."""
from fractions import Fraction as Q
from math import comb


def exp_lower(x, terms=60):
    """Exact rational lower bound for e^x, x > 0 (Taylor partial sum)."""
    s, t = Q(0), Q(1)
    for k in range(terms):
        s += t
        t = t * x / (k + 1)
    return s


def log_upper_ok(m, bound):
    """True iff log m < bound, certified by e^bound > partial sum > m."""
    return exp_lower(bound) > m


def pr3_counts(h, R):
    v = comb(h, 3)
    N, m = v ** 3, h ** 3
    W = 2 * N + 3 * v * v * (R + h + 1)
    L = 3 * v * v * h * (h + 1)
    s = W * m - 2 * N + 2 * L
    eta = Q(W * m - s, W * m)
    return dict(v=v, N=N, m=m, W=W, L=L, s=s, eta=eta)


def pr4_counts(h, R, shared=True):
    v = comb(h, 3)
    N, m = v ** 3, h ** 3
    ell = (h - 1) ** 2 + h
    W = 2 * N + (2 if shared else 3) * v * v * R
    L = 3 * v * v * ell
    s = W * m - 2 * N + 2 * L
    eta = Q(W * m - s, W * m)
    return dict(v=v, N=N, m=m, W=W, L=L, s=s, eta=eta, ell=ell)


def recurrence(tau, sigma, beta, c, lam, lamp):
    chi_max = tau + (1 - beta) * max(sigma - tau, 0)
    chi_old = tau + (1 - beta) * (sigma - tau)
    leaf = sigma + beta * (1 - sigma)
    reserve = max(1 - c, 0)
    return dict(chi_max=chi_max, chi_without_max=chi_old,
                chi_max_equals_tau=(chi_max == tau),
                internal_ok=max(tau, sigma, chi_max) < lam < lamp < 1,
                internal_ok_without_max=max(tau, sigma, chi_old) < lam < lamp < 1,
                leaf_reserve_ok=max(leaf, reserve) < lamp,
                leaf=leaf)
