"""T3: cross-check the E-matrix formula against N = C T D built from the upstream
definitions, the transform identity P_s F_s = 2^{2a^2} B_0 P_t F_t A in the
*new* regime a^{-2} <= theta <= 1/4 (old regime required theta > p/a^4), and the
contraction claims ||S'||<3/4, ||J'||<7/8, ||D'||<1 under only a^2 theta >= 1.
Rigorous Arb balls throughout.
"""
import sys
from fractions import Fraction as Fr
from common import *

setprec(256)
pi = arb.pi()
fails = []
ncases = 0
worstJ = (0, None); worstS = (0, None); worst_id = (None, None)


def gauss_row_sum_matrix(rows_fn, nrows, ncols):
    return [[rows_fn(k, j) for j in range(ncols)] for k in range(nrows)]


def S_matrix(s, t, al):
    # (S u)_k = (1/a) sum_{j in Z} exp(-pi a^-2 (j - s k / t)^2) u_{j mod s}
    W = 12 * al * al + 2 * s
    rows = [[arb(0) for _ in range(s)] for _ in range(t)]
    for k in range(t):
        c = Fr(s * k, t)
        j0 = int(c)
        for j in range(j0 - W, j0 + W + 1):
            rows[k][j % s] += (-pi * A((j - c) ** 2) / (al * al)).exp()
    tail = 4 * (-pi * (W - 1) ** 2 / (al * al)).exp()
    for k in range(t):
        for j in range(s):
            rows[k][j] = (rows[k][j] + arb(0, tail.upper())) / al
    return rows


def T_matrix(s, t, al):
    # (T u)_k = sum_{j in Z} exp(-pi a^2 (t j / s - k)^2) u_{j mod s}
    W = 3 * s + 6
    rows = [[arb(0) for _ in range(s)] for _ in range(t)]
    for k in range(t):
        jc = (k * s) // t
        for j in range(jc - W, jc + W + 1):
            rows[k][j % s] += (-pi * al * al * A((Fr(t * j, s) - k) ** 2)).exp()
    tail = 4 * (-pi * al * al * (W - 2) ** 2).exp()
    for k in range(t):
        for j in range(s):
            rows[k][j] += arb(0, tail.upper())
    return rows


def fourier(q):
    return acb_mat([[acb(A(Fr(-2 * j * k, q))).exp_pi_i() / q for j in range(q)] for k in range(q)])


def perm_s(s, t):  # (P_s u)_j = u_{t j mod s}
    return acb_mat([[1 if c == (t * r) % s else 0 for c in range(s)] for r in range(s)])


def perm_t(s, t):  # (P_t v)_k = v_{-s k mod t}
    return acb_mat([[1 if c == (-s * r) % t else 0 for c in range(t)] for r in range(t)])


def rownorm(M, nr, nc):
    return max(sum((M[i, j].abs_upper() for j in range(nc)), arb(0)) for i in range(nr))


for al in (2, 3, 4):
    a2 = al * al
    for (s, t) in admissible_pairs(26, thmin=Fr(1, a2), thmax=Fr(1, 4)):
        sig = Fr(t, s); th = sig - 1
        ncases += 1
        # E formula vs direct N - I
        E1 = arb_mat(E_matrix(s, t, al, H=8))
        N2 = arb_mat(N_matrix_direct(s, t, al, Jwin=4))
        Id = arb_mat([[1 if i == j else 0 for j in range(s)] for i in range(s)])
        D = N2 - Id - E1
        for i in range(s):
            for j in range(s):
                if not D[i, j].contains(0):
                    fails.append(("E formula", s, t, al, i, j))
        # T, C, D -> N
        Tm = T_matrix(s, t, al)
        Cq = [ (2 * t * j + s) // (2 * s) for j in range(s)]
        N3 = arb_mat([[Tm[Cq[l]][j] * (pi * a2 * A(beta_of(s, t, j) ** 2)).exp() for j in range(s)] for l in range(s)])
        D3 = N3 - N2
        for i in range(s):
            for j in range(s):
                if not D3[i, j].contains(0):
                    fails.append(("N via T", s, t, al, i, j))
        # norms
        Ninv = N2.inv()
        nJ = rownorm(Ninv, s, s) / 2
        if not nJ < arb(7) / 8:
            fails.append(("||J'||<7/8", s, t, al, nJ))
        if float(nJ.mid()) > worstJ[0]:
            worstJ = (float(nJ.mid()), (s, t, al))
        nE = rownorm(E1, s, s)
        if not nE < arb("0.42"):
            fails.append(("||N-I||<0.42", s, t, al))
        Sm = S_matrix(s, t, al)
        nS = max(sum(Sm[k], arb(0)) for k in range(t)) / 2
        if not nS < arb(3) / 4:
            fails.append(("||S'||<3/4", s, t, al))
        if float(nS.mid()) > worstS[0]:
            worstS = (float(nS.mid()), (s, t, al))
        nD = arb(2) ** (2 - 2 * a2) * (pi * a2 / 4).exp()
        if not nD < 1:
            fails.append(("||D'||<1", s, t, al))
        # identity: P_s F_s = 2^{2a^2} D' J' C P_t F_t S'  (= D N^{-1} C P_t F_t S)
        Sc = acb_mat(arb_mat(Sm))
        Dm = acb_mat([[ (pi * a2 * A(beta_of(s, t, j) ** 2)).exp() if i == j else 0 for j in range(s)] for i in range(s)])
        Cm = acb_mat([[1 if c == Cq[r] else 0 for c in range(t)] for r in range(s)])
        lhs = perm_s(s, t) * fourier(s)
        rhs = Dm * acb_mat(Ninv) * Cm * perm_t(s, t) * fourier(t) * Sc
        diff = lhs - rhs
        mx = max(diff[i, j].abs_upper() for i in range(s) for j in range(s))
        if not mx < arb(2) ** -60:
            fails.append(("identity", s, t, al, mx))
        if worst_id[0] is None or mx > worst_id[0]:
            worst_id = (mx, (s, t, al))
    print(f"alpha={al} done, cases so far {ncases}", flush=True)

print("cases:", ncases)
print("max ||J'|| seen:", worstJ, " max ||S'|| seen:", worstS)
print("max |identity residual| (upper bound):", worst_id)
print("fails:", fails[:20])
print("RESULT:", "FAIL" if fails else "PASS")
sys.exit(1 if fails else 0)
