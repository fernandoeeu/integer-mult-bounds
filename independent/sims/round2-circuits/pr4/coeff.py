"""Exact coefficient-map checks (Fractions; no floating point)."""
from fractions import Fraction


def side_matrix(C):
    """{target: {source: exact coefficient}} of J L V (designated outputs)."""
    sup = C.supports()
    M = {}
    for z, t, c in C.outputs:
        row = M.setdefault(t, {})
        for s, mult in sup[z].items():
            row[s] = row.get(s, 0) + c * mult
    return M


def check_side_map(C, central=True):
    """Check central + side == identity for every (S,T).

    central=True: central coefficient (|S cap T|-1)/2 supplied by the
    original gather/scatter; the side map must then be +1/2 (disjoint),
    -1/2 (|S cap T|=2), 0 otherwise.  Returns (ok, n_nonzero, failures)."""
    M = side_matrix(C)
    T = C.T
    fails = []
    nnz = 0
    for si, S in enumerate(T):
        row = M.get(si, {})
        for ti, Tm in enumerate(T):
            j = (S & Tm).bit_count()
            want = Fraction(0)
            if ti != si:
                if j == 0:
                    want = Fraction(1, 2)
                elif j == 2:
                    want = Fraction(-1, 2)
            got = row.get(ti, Fraction(0))
            if got != 0:
                nnz += 1
            if got != want:
                fails.append((si, ti, got, want))
                if len(fails) > 20:
                    return False, nnz, fails
            cen = Fraction(j - 1, 2)
            if ti == si:
                if cen + got != 1:
                    fails.append(('diag', si, cen + got))
            elif cen + got != 0:
                fails.append(('off', si, ti, cen + got))
    return not fails, nnz, fails
