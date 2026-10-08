"""Exact arithmetic re-derivation of the claimed counts and savings.

PR 6 (notes/aligned-bit-note.tex, aligned-bit-construction.tex):
  R = c+q+h = 494196, W = 2N + 2v^2 R = 394759742720000,
  s = W m - N + 6 v^2 h(h-1) = 49344965957616000000, Wm - s = 1882384000000,
  eta = 49/1284490000 > (325/10^11)(11737/1000), log m < 11737/1000.
PR 4 head (docs/research/shared-retained-complex.md, patch section):
  C=66638, q=24312, R=90950, W=761750114048, L=6796219584, D=2990500480,
  s=10530430586099072, eta=365/1285272576,
  eta-(2970/10^11)(477/50)=406952569/627574500000000000, log m < 477/50,
  gates 3v^2(8v+4C+4+2(h-6)) = 3475338442752 < 12W, s < m^5.
log m < L is proved by m < sum_{k<=K} L^k/k! (a lower bound for e^L).
"""
import sys
from fractions import Fraction as Q
from math import comb, factorial


def log_lt(m, L, K=80):
    s = sum(L ** k / factorial(k) for k in range(K + 1))
    return m < s


def pr6(c, q):
    h = 50
    v = comb(h, 3); N = v ** 3; m = h ** 3
    R = c + q + h
    W = 2 * N + 2 * v * v * R
    s = W * m - N + 6 * v * v * h * (h - 1)
    eta = Q(W * m - s, W * m)
    a, L0 = Q(325, 10 ** 11), Q(11737, 1000)
    out = dict(R=R, R_claim=R == 494196, W=W, W_claim=W == 394759742720000,
               s=s, s_claim=s == 49344965957616000000, gap=W * m - s, gap_claim=W * m - s == 1882384000000,
               eta=eta, eta_claim=eta == Q(49, 1284490000), eta_gt=eta > a * L0, log_ok=log_lt(m, L0))
    # old center loss h^2 with the same roles: would it certify? (PR's own remark)
    s_old = W * m - N + 6 * v * v * h * h
    out['same_roles_old_loss_certifies'] = Q(W * m - s_old, W * m) > a * L0
    # windows quoted in the note
    eps, lamp, beta, ac = Q(49999, 100000), 1 - Q(3249, 10 ** 12), Q(19, 25), Q(14, 10 ** 9)
    kappa = Q(1624, 10 ** 12)
    out['g3'] = eps * (1 - lamp)
    out['g3_claim'] = out['g3'] == Q(162446751, 10 ** 17)
    out['g3_gt_kappa'] = out['g3'] > kappa
    out['leaf_window'] = (1 - beta) * ac > 1 - lamp
    out['guard_beta'] = beta > Q(3, 4)
    out['kappa_lt_a_over_2'] = kappa < a / 2
    out['dyadic'] = Q(1, 2 ** 30) < kappa < Q(1, 2 ** 29)
    return out


def pr4(C, q):
    h = 24
    v = comb(h, 3); N = v ** 3; m = h ** 3
    R = C + q
    W = 2 * N + 2 * v * v * R
    ell = (h - 1) ** 2 + h
    L = 3 * v * v * ell
    D = 2 * N - 2 * L
    s = W * m - D
    eta = Q(D, W * m)
    a = Q(2970, 10 ** 11)
    gates = 3 * v * v * (8 * v + 4 * C + 4 + 2 * (h - 6))
    return dict(R=R, R_claim=R == 90950, W=W, W_claim=W == 761750114048, ell=ell,
                L_claim=L == 6796219584, D_claim=D == 2990500480, s_claim=s == 10530430586099072,
                eta=eta, eta_claim=eta == Q(365, 1285272576),
                slack_claim=eta - a * Q(477, 50) == Q(406952569, 627574500000000000),
                slack_pos=eta - a * Q(477, 50) > 0, log_ok=log_lt(m, Q(477, 50)),
                gates=gates, gates_claim=gates == 3475338442752, gates_lt_12W=gates < 12 * W,
                s_lt_m5=2 <= s < m ** 5)


if __name__ == '__main__':
    c6, q6, C4, q4 = map(int, sys.argv[1:5])
    ok = True
    for name, d in (('PR6', pr6(c6, q6)), ('PR4', pr4(C4, q4))):
        print(name)
        for k, x in d.items():
            print('  ', k, x)
            if isinstance(x, bool) and k != 'same_roles_old_loss_certifies':
                ok &= x
    print('ARITH', 'PASS' if ok else 'FAIL')
    sys.exit(0 if ok else 1)
