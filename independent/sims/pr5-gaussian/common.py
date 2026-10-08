"""Shared exact / rigorous helpers for the PR 5 fast-Gaussian checks.

Independent of the PR's scripts. All pass/fail comparisons use exact
rationals (fractions.Fraction / flint.fmpq) or Arb ball arithmetic
(python-flint), where `a < b` is True only when certified.
"""
from fractions import Fraction as Fr
from math import gcd, isqrt
import flint
from flint import arb, acb, fmpq, fmpz, arb_mat, acb_mat, ctx


def setprec(bits):
    ctx.prec = bits


def A(x):
    """Exact rational -> arb."""
    x = Fr(x)
    return arb(fmpq(x.numerator, x.denominator))


def q_of(s, t, j):
    # q_j = floor(t j / s + 1/2), valid for every integer j
    return (2 * t * j + s) // (2 * s)


def beta_of(s, t, j):
    return Fr(t * j, s) - q_of(s, t, j)


def X_of(s, t, l, h):
    """X_{l,h} = (sigma h + beta_l)^2 - beta_{l+h}^2 (exact)."""
    sig = Fr(t, s)
    return (sig * h + beta_of(s, t, l)) ** 2 - beta_of(s, t, l + h) ** 2


def ceil_sqrt(n):
    r = isqrt(n)
    return r if r * r == n else r + 1


def admissible_pairs(smax, thmin=None, thmax=None, strict_max=False):
    """Coprime (s,t), 2<=s<t, theta=t/s-1 in [thmin, thmax]."""
    out = []
    for s in range(2, smax + 1):
        for t in range(s + 1, 2 * s + 1):
            if gcd(s, t) != 1:
                continue
            th = Fr(t - s, s)
            if thmin is not None and th < thmin:
                continue
            if thmax is not None and (th > thmax or (strict_max and th >= thmax)):
                continue
            out.append((s, t))
    return out


def E_matrix(s, t, alpha, H=8):
    """Rigorous arb enclosure of the s x s matrix E = N - I.

    E[l][r] = sum_{h != 0, h = r-l mod s} exp(-pi alpha^2 X_{l,h}).
    Terms with |h| <= H are summed; the remainder uses
    X_{l,h} >= |h|(|h|-1) (since |sigma h + beta_l| >= |h| - 1/2 and
    beta^2 <= 1/4), so the tail of one row is at most
    4 exp(-pi alpha^2 H (H+1)); this is added as a radius to every entry.
    """
    a2 = alpha * alpha
    pi = arb.pi()
    rows = [[arb(0) for _ in range(s)] for _ in range(s)]
    for l in range(s):
        for h in range(-H, H + 1):
            if h == 0:
                continue
            X = X_of(s, t, l, h)
            assert X >= 0
            rows[l][(l + h) % s] += (-pi * a2 * A(X)).exp()
    tail = 4 * (-pi * a2 * H * (H + 1)).exp()
    tail_ball = arb(0, tail.upper())
    for l in range(s):
        for r in range(s):
            rows[l][r] += tail_ball
    return rows


def N_matrix_direct(s, t, alpha, Jwin=8):
    """N = C T D built straight from the upstream definitions (no X formula).

    (Nu)_l = sum_{j in Z} exp(-pi a^2 (t j/s - q_l)^2) exp(pi a^2 beta_{j mod s}^2) u_{j mod s}
    Window |j - l| <= Jwin*s plus a crude rigorous tail.
    """
    a2 = alpha * alpha
    pi = arb.pi()
    sig = Fr(t, s)
    rows = [[arb(0) for _ in range(s)] for _ in range(s)]
    W = Jwin * s
    for l in range(s):
        ql = q_of(s, t, l)
        for j in range(l - W, l + W + 1):
            jm = j % s
            e = (sig * j - ql) ** 2 - beta_of(s, t, jm) ** 2
            rows[l][jm] += (-pi * a2 * A(e)).exp()
    # tail |j-l| > W: exponent >= (|j-l| - 1/2)^2 - 1/4 >= W(W+1)
    tail = 4 * (-pi * a2 * W * (W + 1)).exp()
    tb = arb(0, tail.upper())
    for l in range(s):
        for r in range(s):
            rows[l][r] += tb
    return rows


def lg2(x):
    return x.log() / arb(2).log()
