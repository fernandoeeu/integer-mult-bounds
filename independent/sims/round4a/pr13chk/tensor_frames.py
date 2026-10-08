"""PR 13, stage-two auxiliary source frames: exact rational checks at small h,
written from notes/source-frame-bit.tex (lemmas scratch-source-frames and
source-frame-basis) and notes/projector-batching.tex.

F = Q^h with label form H = I - (2/25)J (PR 7); tensor form H (x) H (x) H on
Q^{h^3}.  t_a = indicator of a five-set a.  Stage two: A = F,
P = <t_a1>, B = P^perp (form-orthogonal), Q = <t_a3>.
D0 = B (x) F (x) Q, D1 = A (x) F (x) Q.  Orthogonal projector onto a
nondegenerate U: P_U = U (U^T G U)^{-1} U^T G.

Checks for every ordered pair (a1, a3) of five-sets:
 F1 D0, D1, D1^perp nondegenerate; D0 subset D1; dims (h-1)h and h^2
 F2 source P_D0, sink I+P_D0: endpoint difference I; entrance P_D0-P_D0 = 0
 F3 exit E = I + P_D0 - P_D1 is idempotent, rank m-h, kernel = P (x) F (x) Q,
    and E equals the orthogonal projector onto D0 (+) D1^perp
 F4 (basis lemma) with one random S = T(I_F (x) K) from PR 10's family in the
    reordered coordinates (third factor slow): the first-h-row/last-h-column
    corner of S E S^{-1} is nonsingular for EVERY (a1, a3); and the batching
    Schur complement middle block equals I_{m-2h} exactly (pivot profile:
    h corner pivots + one contiguous identity block).
Negative controls: wrong source frame (P_D1), a non-nested pair (Q changed
in D0), and a degenerate S (K = identity, G_i = identity) must fail.
Usage: python3 tensor_frames.py h [seed] [--schur N]
"""
import sys, random, json
from fractions import Fraction as Fr
from itertools import combinations

h = int(sys.argv[1]); seed = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2][0] != '-' else 1
nschur = int(sys.argv[sys.argv.index('--schur') + 1]) if '--schur' in sys.argv else 2
m = h ** 3; Hd = h * h
ALPHA = Fr(2, 25)
rnd = random.Random(seed)

# ---------------------------------------------------------- exact linear algebra
def matmul(A, B):
    Bt = list(zip(*B))
    return [[sum(a * b for a, b in zip(r, c) if a and b) for c in Bt] for r in A]

def rank(M):
    M = [list(r) for r in M]; rk = 0; cols = len(M[0]) if M else 0
    for c in range(cols):
        p = next((i for i in range(rk, len(M)) if M[i][c]), None)
        if p is None: continue
        M[rk], M[p] = M[p], M[rk]
        pv = M[rk][c]
        for i in range(len(M)):
            if i != rk and M[i][c]:
                f = M[i][c] / pv
                M[i] = [x - f * y for x, y in zip(M[i], M[rk])]
        rk += 1
    return rk

def inv(M):
    n = len(M); A = [list(r) + [Fr(int(i == j)) for j in range(n)] for i, r in enumerate(M)]
    for c in range(n):
        p = next(i for i in range(c, n) if A[i][c])
        A[c], A[p] = A[p], A[c]
        pv = A[c][c]; A[c] = [x / pv for x in A[c]]
        for i in range(n):
            if i != c and A[i][c]:
                f = A[i][c]; A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    return [r[n:] for r in A]

def T(M): return [list(r) for r in zip(*M)]

# ---------------------------------------------------------- F level
HF = [[Fr(int(i == j)) - ALPHA for j in range(h)] for i in range(h)]
five = [c for c in combinations(range(h), 5)]
def tvec(a): return [Fr(1) if i in a else Fr(0) for i in range(h)]

def perp_F(vecs):           # form-orthogonal complement in F
    rows = matmul(vecs, HF) if vecs else []
    # null space of rows
    n = h; M = [list(r) for r in rows]; piv = []; rk = 0
    for c in range(n):
        p = next((i for i in range(rk, len(M)) if M[i][c]), None)
        if p is None: continue
        M[rk], M[p] = M[p], M[rk]; pv = M[rk][c]; M[rk] = [x / pv for x in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c]:
                f = M[i][c]; M[i] = [x - f * y for x, y in zip(M[i], M[rk])]
        piv.append(c); rk += 1
    out = []
    for f in range(n):
        if f in piv: continue
        x = [Fr(0)] * n; x[f] = Fr(1)
        for r, p in zip(M, piv): x[p] = -r[f]
        out.append(x)
    return out

def kron(u, v): return [a * b for a in u for b in v]
def tensor_span(A, Bs, C):  # spans as lists of vectors; order (factor1, factor2, factor3), factor1 slowest
    return [kron(kron(a, b), c) for a in A for b in Bs for c in C]

E_F = [[Fr(int(i == j)) for j in range(h)] for i in range(h)]

def gram_apply(U):          # rows of U^T G (G = HF^{(x)3}), each U column given as a row vector here
    out = []
    for u in U:
        # apply HF on each factor
        x = u
        # factor 3 (fastest)
        y = [Fr(0)] * m
        for i in range(h * h):
            blk = x[i * h:(i + 1) * h]
            s = sum(blk)
            for k in range(h): y[i * h + k] = blk[k] - ALPHA * s
        x = y; y = [Fr(0)] * m
        for i in range(h):
            for k in range(h):
                s = sum(x[i * h * h + j * h + k] for j in range(h))
                for j in range(h): y[i * h * h + j * h + k] = x[i * h * h + j * h + k] - ALPHA * s
        x = y; y = [Fr(0)] * m
        for j in range(h * h):
            s = sum(x[i * h * h + j] for i in range(h))
            for i in range(h): y[i * h * h + j] = x[i * h * h + j] - ALPHA * s
        out.append(y)
    return out

def projector(U):           # U: list of basis vectors (rows). returns m x m P_U
    UG = gram_apply(U)                         # k x m  (= U^T G)
    gram = matmul(UG, T(U))                    # k x k
    if rank(gram) < len(U): return None
    Gi = inv(gram)
    return matmul(T(U), matmul(Gi, UG))        # m x m

def ident(n): return [[Fr(int(i == j)) for j in range(n)] for i in range(n)]
def add(A, B, s=1): return [[a + s * b for a, b in zip(r, q)] for r, q in zip(A, B)]

res = dict(h=h, m=m, pairs=0, F1=True, F2=True, F3=True, F4_corner=True, F4_schur=True, schur_checked=0)
fails = []

# ---------------------------------------------------------- PR 10 family S, reordered coordinates
# reordered coordinates (alpha, i): alpha = original third factor (slow), i = (f1, f2) fast.
def reorder_index(x):       # original index (f1,f2,f3) -> reordered (f3, f1, f2)
    f1, r = divmod(x, h * h); f2, f3 = divmod(r, h)
    return f3 * h * h + f1 * h + f2

RANGE = int(__import__("os").environ.get("RANGE", "3"))
def rand_inv(n, lo=-RANGE, hi=RANGE):
    while True:
        M = [[Fr(rnd.randint(lo, hi)) for _ in range(n)] for _ in range(n)]
        if rank(M) == n: return M

def build_S(K, G):          # S = T(I_F (x) K): (I (x) K) acts on fast index i, then G_i on alpha
    S = [[Fr(0)] * m for _ in range(m)]
    for al in range(h):
        for i in range(Hd):
            for be in range(h):
                g = G[i][al][be]
                if not g: continue
                for j in range(Hd):
                    k = K[i][j]
                    if k: S[al * Hd + i][be * Hd + j] += g * k
    return S

K = rand_inv(Hd); G = [rand_inv(h) for _ in range(Hd)]
S = build_S(K, G) if h == 5 else None; Sinv = inv(S) if h == 5 else None
Kd = ident(Hd); Gd = [ident(h) for _ in range(Hd)]          # negative control: degenerate member
Sd = build_S(Kd, Gd) if h == 5 else None; Sdinv = Sd

def permute(M):             # conjugate by reordering permutation
    perm = [reorder_index(x) for x in range(m)]
    out = [[Fr(0)] * m for _ in range(m)]
    for x in range(m):
        row = M[x]; px = perm[x]
        for y in range(m):
            if row[y]: out[px][perm[y]] = row[y]
    return out

def corner(M, r):
    return [row[m - r:] for row in M[:r]]

def schur_ok(M, r):
    Lr, Mr, Rr = range(r), range(r, m - r), range(m - r, m)
    PLR = [[M[i][j] for j in Rr] for i in Lr]
    PLRi = inv(PLR)
    PMR = [[M[i][j] for j in Rr] for i in Mr]
    PLM = [[M[i][j] for j in Mr] for i in Lr]
    PMM = [[M[i][j] for j in Mr] for i in Mr]
    Sch = add(PMM, matmul(PMR, matmul(PLRi, PLM)), -1)
    return Sch == ident(m - 2 * r)


def S_apply_col(u):          # S u for u in reordered coords: (I(x)K) on fast index, then G_i on alpha
    y = [Fr(0)] * m
    for al in range(h):
        for i in range(Hd):
            y[al * Hd + i] = sum(K[i][j] * u[al * Hd + j] for j in range(Hd) if u[al * Hd + j])
    z = [Fr(0)] * m
    for i in range(Hd):
        for al in range(h):
            z[al * Hd + i] = sum(G[i][al][be] * y[be * Hd + i] for be in range(h))
    return z

Kinv = inv(K); Ginv = [inv(g) for g in G]
def row_Sinv(x):             # x S^{-1} = (x (I(x)K^{-1})) T^{-1}; T^{-1} applies G_i^{-1} on alpha at fixed i
    y = [Fr(0)] * m
    for al in range(h):
        for j in range(Hd):
            y[al * Hd + j] = sum(x[al * Hd + i] * Kinv[i][j] for i in range(Hd) if x[al * Hd + i])
    z = [Fr(0)] * m
    for i in range(Hd):
        for be in range(h):
            z[be * Hd + i] = sum(y[al * Hd + i] * Ginv[i][al][be] for al in range(h))
    return z

def reorder_vec(u):
    out = [Fr(0)] * m
    for x in range(m): out[reorder_index(x)] = u[x]
    return out

def factored_corner(a1, a3):
    tP, tQ = tvec(a1), tvec(a3)
    U = [kron(kron(tP, e), tQ) for e in E_F]          # basis of ker E = P (x) F (x) Q (original order)
    UG = gram_apply(U)
    Vp = matmul(inv(matmul(UG, T(U))), UG)             # V' with V'U = I
    Ur = [reorder_vec(u) for u in U]; Vr = [reorder_vec(x) for x in Vp]
    SU = [S_apply_col(u) for u in Ur]                  # h columns
    VS = [row_Sinv(x) for x in Vr]                     # h rows
    left = [[SU[c][r] for c in range(h)] for r in range(h)]          # first h rows of S U
    right = [[VS[r][m - h + c] for c in range(h)] for r in range(h)] # last h cols of V' S^{-1}
    return [[-x for x in row] for row in matmul(left, right)]

ctrl = dict(wrong_source_rejected=None, non_nested_rejected=None, degenerate_S_rejected=None)
first = True
if h >= 6:
    for a1 in five:
        for a3 in five:
            res['pairs'] += 1
            c = factored_corner(a1, a3)
            if rank(c) != h:
                res['F4_corner'] = False; fails.append(('F4 corner singular', a1, a3))
    res['F1'] = res['F2'] = res['F3'] = res['F4_schur'] = 'not run (h>=6: factored corner only)'
    K, G = Kd, Gd; Kinv = inv(K); Ginv = [inv(g) for g in G]
    ctrl = dict(degenerate_S_rejected=rank(factored_corner(five[0], five[-1])) < h)
    res['controls'] = ctrl; res['fails'] = fails[:5]
    res['PASS'] = res['F4_corner'] is True and ctrl['degenerate_S_rejected']
    print(json.dumps(res)); sys.exit(0 if res['PASS'] else 1)
for a1 in five:
    for a3 in five:
        res['pairs'] += 1
        tP, tQ = tvec(a1), tvec(a3)
        Bsp = perp_F([tP])
        D0 = tensor_span(Bsp, E_F, [tQ]); D1 = tensor_span(E_F, E_F, [tQ])
        D1p = tensor_span(E_F, E_F, perp_F([tQ]))
        P0, P1, P1p = projector(D0), projector(D1), projector(D1p)
        if P0 is None or P1 is None or P1p is None:
            res['F1'] = False; fails.append(('degenerate', a1, a3)); continue
        I = ident(m)
        nested = rank(D1 + D0) == len(D1) and len(D0) == (h - 1) * h and len(D1) == h * h
        res['F1'] &= nested
        src, snk = P0, add(I, P0)
        res['F2'] &= add(snk, src, -1) == I and add(P0, src, -1) == [[0] * m for _ in range(m)]
        E = add(snk, P1, -1)
        idem = matmul(E, E) == E
        rk = rank(E)
        ker = tensor_span([tP], E_F, [tQ])
        kerok = all(all(x == 0 for x in col) for col in T(matmul(E, T(ker))))
        orth = projector(D0 + D1p)
        Fok = idem and rk == m - h and kerok and orth == E
        res['F3'] &= Fok
        if not Fok: fails.append(('F3', a1, a3, idem, rk, kerok, orth == E))
        # F4 basis lemma, reordered coordinates
        Er = permute(E)
        SE = matmul(S, matmul(Er, Sinv))
        cnr = rank(corner(SE, h)) == h
        res['factored_corner_matches_full'] = factored_corner(a1, a3) == corner(SE, h)
        res['F4_corner'] &= cnr
        if not cnr: fails.append(('F4 corner singular', a1, a3))
        if cnr and res['schur_checked'] < nschur:
            so = schur_ok(SE, h); res['F4_schur'] &= so; res['schur_checked'] += 1
        if first:
            first = False
            # controls on the first pair
            Ew = add(add(I, P1), P1, -1)          # source P_D1: exit becomes I (rank m), entrance P_D0 - P_D1 != 0
            ctrl['wrong_source_rejected'] = not (rank(Ew) == m - h) and add(P0, P1, -1) != [[0] * m for _ in range(m)]
            other = tvec(five[1]) if len(five) > 1 else [Fr(1)] * h
            D0x = tensor_span(Bsp, E_F, [other]); P0x = projector(D0x)
            if P0x is not None:
                Ex = add(add(I, P0x), P1, -1)
                ctrl['non_nested_rejected'] = not (matmul(Ex, Ex) == Ex and rank(Ex) == m - h)
            SdE = matmul(Sd, matmul(Er, Sdinv))
            ctrl['degenerate_S_rejected'] = rank(corner(SdE, h)) < h
res['controls'] = ctrl
res['fails'] = fails[:5]
res['PASS'] = all(res[k] for k in ('F1', 'F2', 'F3', 'F4_corner', 'F4_schur')) and all(v is not False for v in ctrl.values())
print(json.dumps(res))
