"""Exact phase-frame check (Gaussian phases as exponents mod 4).

For nondegenerate U, q_U(x) = wt(P_U x) mod 4 with P_U the F_2 projection.
The frame C_U = H diag(i^{q_U}) H, and the kernel aI+bX_v = H diag(i^{[v.x]}) H
(since a + b(-1)^{v.x} is 1 or i), so the edge identity
  C_V C_U^{-1} = prod_{v in onb} (aI+bX_v)^{+-1}
is equivalent, exactly, to i^{q_V(x)-q_U(x)} = prod_v i^{eps_v [v.x]} for all
x, with eps_v = +-1 = wt(v) mod 4 times the edge direction.  We verify this
for every x in F_2^h.
"""
from f2 import Space, dot, orthonormal_basis, residual


def projector(U):
    b = U.basis()
    k = len(b)
    # Gram matrix and its inverse over F_2 (Gauss-Jordan on [G | I])
    rows = []
    for i in range(k):
        r = 0
        for j in range(k):
            if dot(b[i], b[j]):
                r |= 1 << j
        rows.append(r | (1 << (k + i)))
    for col in range(k):
        piv = next(i for i in range(col, k) if rows[i] >> col & 1)
        rows[col], rows[piv] = rows[piv], rows[col]
        for i in range(k):
            if i != col and rows[i] >> col & 1:
                rows[i] ^= rows[col]
    Ginv = [rows[i] >> k for i in range(k)]

    def P(x):
        y = [dot(bj, x) for bj in b]
        out = 0
        for i in range(k):
            ci = 0
            for j in range(k):
                if Ginv[i] >> j & 1:
                    ci ^= y[j]
            if ci:
                out ^= b[i]
        return out
    return P


def check_edge(U, V, h):
    """U subset V nondegenerate; returns True iff the identity holds for all x
    with the constructed orthonormal basis of the residual (increasing edge;
    a decreasing edge is the same identity negated)."""
    E = residual(U, V)
    onb = orthonormal_basis(E) if E.dim() else []
    if onb is None:
        return False
    PU, PV = projector(U), projector(V)
    for x in range(1 << h):
        lhs = (PV(x).bit_count() - PU(x).bit_count()) % 4
        rhs = sum(v.bit_count() * dot(v, x) for v in onb) % 4
        if lhs != rhs:
            return False
    return True


def run_from_checker(ec, labels, h, limit=None):
    """Verify the identity for every distinct F-level residual pair the edge
    checker has seen (both parts)."""
    n = ok = 0
    for (k1, k2), info in ec.res_cache.items():
        sign, d, good, why = info
        if not good:
            continue
        U, V = labels.space(k1), labels.space(k2)
        if sign < 0:
            U, V = V, U
        if not V.contains_space(U):
            continue
        n += 1
        if check_edge(U, V, h):
            ok += 1
        if limit and n >= limit:
            break
    return n, ok
