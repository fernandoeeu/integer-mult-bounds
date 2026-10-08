"""Exact linear algebra helpers (Fractions) and the upstream lower-lower
elimination (04-swap.tex, Lemma lower-lower): topmost nonzero active row,
its rightmost nonzero active entry; clear left by lower-triangular column
ops, clear below by lower-triangular row ops, scale pivot to one."""
from fractions import Fraction as Q
import random

def eye(n): return [[Q(int(i == j)) for j in range(n)] for i in range(n)]
def zeros(n, k=None): return [[Q(0)]*(k or n) for _ in range(n)]
def mul(A, B):
    Bt = list(zip(*B))
    return [[sum((a*b for a, b in zip(r, c) if a and b), Q(0)) for c in Bt] for r in A]
def add(A, B, s=1): return [[a + s*b for a, b in zip(r, t)] for r, t in zip(A, B)]
def kron(A, B):
    return [[a*b for a in ra for b in rb] for ra in A for rb in B]
def T(A): return [list(r) for r in zip(*A)]
def scal(c, A): return [[c*a for a in r] for r in A]

def inv(A):
    n = len(A); M = [list(r) + [Q(int(i == j)) for j in range(n)] for i, r in enumerate(A)]
    for c in range(n):
        p = next((i for i in range(c, n) if M[i][c]), None)
        if p is None: raise ZeroDivisionError('singular')
        M[c], M[p] = M[p], M[c]
        pv = M[c][c]; M[c] = [x/pv for x in M[c]]
        for i in range(n):
            if i != c and M[i][c]:
                f = M[i][c]; M[i] = [x - f*y for x, y in zip(M[i], M[c])]
    return [r[n:] for r in M]

def rank(A):
    M = [list(r) for r in A]; rk = 0; n, k = len(M), len(M[0])
    for c in range(k):
        p = next((i for i in range(rk, n) if M[i][c]), None)
        if p is None: continue
        M[rk], M[p] = M[p], M[rk]
        for i in range(rk+1, n):
            if M[i][c]:
                f = M[i][c]/M[rk][c]; M[i] = [x - f*y for x, y in zip(M[i], M[rk])]
        rk += 1
    return rk

def det_nonzero(A): return rank(A) == len(A)

def lower_lower(A):
    """returns (E1, Pi, E2, pivots) with A = E1 Pi E2, E1,E2 invertible lower
    triangular; pivots in elimination order as (row, col)."""
    m = len(A); M = [list(r) for r in A]
    L = eye(m); R = eye(m)               # L A R = Pi
    arow, acol = set(range(m)), set(range(m)); piv = []
    while True:
        i = next((i for i in sorted(arow) if any(M[i][j] for j in acol)), None)
        if i is None: break
        j = max(jj for jj in acol if M[i][jj])
        pv = M[i][j]
        for k in sorted(acol):           # clear left (columns k<j)
            if k < j and M[i][k]:
                f = M[i][k]/pv
                for rr in range(m): M[rr][k] -= f*M[rr][j]
                for rr in range(m): R[rr][k] -= f*R[rr][j]
        for l in sorted(arow):           # clear below
            if l > i and M[l][j]:
                f = M[l][j]/pv
                M[l] = [x - f*y for x, y in zip(M[l], M[i])]
                L[l] = [x - f*y for x, y in zip(L[l], L[i])]
        M[i] = [x/pv for x in M[i]]; L[i] = [x/pv for x in L[i]]
        arow.discard(i); acol.discard(j); piv.append((i, j))
    Pi = zeros(m)
    for i, j in piv: Pi[i][j] = Q(1)
    assert M == Pi, 'elimination did not reach Pi'
    for X in (L, R):
        for a in range(m):
            for b in range(a+1, m): assert X[a][b] == 0
    E1, E2 = inv(L), inv(R)
    return E1, Pi, E2, piv

def classify_pivots(piv, m, a):
    """Check the PR10 profile: r=m-a pivots in L x R, then diagonal (i,i) on M.
    Returns (ok, corner_matched_order)."""
    r = m - a
    Lr, Rr = set(range(r)), set(range(m-r, m))
    corner = [p for p in piv if p[0] in Lr]
    rest = [p for p in piv if p[0] not in Lr]
    ok = len(piv) == a and len(corner) == r and all(j in Rr for _, j in corner) \
        and sorted(rest) == [(i, i) for i in range(r, m-r)] and piv[:r] == corner
    matched = sorted(corner) == [(k, m-r+k) for k in range(r)]
    return ok, matched
