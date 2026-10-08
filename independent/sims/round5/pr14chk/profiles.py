"""PR 14 (1fa5b9a) and PR 16 (a80f5e6, --nested): one controlled basis S = T(I_F (x) K) vs the SIX pivot profiles
claimed simultaneously (source-frame exit + join + refined stage-3 data entrance +
stage-2 data entrance), built from the notes with realistic labels: k-subset
vectors of F = Q^h, label form G = I - alpha J, ORTHOGONAL projectors for that
form (not coordinate projectors as in the PR's own matrix_checks.py).
Coordinates: slow index a = third factor F (h values), fast index i in V = F(x)F (H values).
For each instance A and its transpose: P = S A S^-1 mod p, run the lower/lower
elimination (row i top-down, pivot = rightmost nonzero, row ops downward, column ops
leftward) and check the claimed contiguous pivots are present and the singleton count.
Mod p = 16777213; a full-rank pivot found mod p is one over Q only generically, so
PASS is a screen, a FAIL for every random S would indicate an identically-zero condition.
usage: profiles.py h k c0 n_inst seed  (form I-(c0/k^2)J makes |A&C|=c0 pairs orthogonal) [--mut=coord]"""
import sys, random, itertools, numpy as np
p = 16777213
h, k, c0, n_inst, seed = map(int, sys.argv[1:6]); MUT = [a for a in sys.argv[6:] if a.startswith('--mut=')]
MUT = MUT[0][6:] if MUT else ''
NESTED = '--nested' in sys.argv     # PR 16: K = T_2(I_F1 (x) K0), T_2 acts by J_beta on F1 at F2-coordinate beta
rng = random.Random(seed); H = h*h; m = h*H; r = h-1
def inv_mod(A):
    n = len(A); M = np.concatenate([A % p, np.eye(n, dtype=np.int64)], 1)
    for c in range(n):
        rr = next(i for i in range(c, n) if M[i, c]); M[[c, rr]] = M[[rr, c]]
        M[c] = M[c] * pow(int(M[c, c]), -1, p) % p
        f = M[:, c].copy(); f[c] = 0; M = (M - np.outer(f, M[c]) % p) % p
    return M[:, n:]
mm = lambda A, B: (A @ B) % p
def factor(P):
    M = P.copy() % p; piv = []
    for i in range(m):
        nz = np.nonzero(M[i])[0]
        if len(nz) == 0: continue
        j = int(nz[-1]); piv.append((i, j))
        M[i] = M[i] * pow(int(M[i, j]), -1, p) % p
        col = M[i+1:, j].copy(); M[i+1:] = (M[i+1:] - np.outer(col, M[i]) % p) % p
        rowl = M[i, :j].copy(); M[:, :j] = (M[:, :j] - np.outer(M[:, j], rowl) % p) % p
    assert all(np.count_nonzero(M[i]) <= 1 for i in range(m))
    return piv
alpha = c0 * pow(k*k, -1, p) % p
G = (np.eye(h, dtype=np.int64) - alpha) % p; GG = np.kron(G, G) % p
IF = np.eye(h, dtype=np.int64); IV = np.eye(H, dtype=np.int64); I = np.eye(m, dtype=np.int64)
sets = list(itertools.combinations(range(h), k))
vec = lambda s: np.array([1 if x in s else 0 for x in range(h)], dtype=np.int64)
def proj_line(t, Gm):
    if MUT == 'coord':                       # mutant: coordinate projector onto e_0 regardless of label
        e = np.zeros(len(t), dtype=np.int64); e[0] = 1; return np.outer(e, e)
    Gt = mm(Gm, t.reshape(-1, 1)).ravel(); n = int(t @ Gt % p); assert n
    return np.outer(t, Gt) % p * pow(n, -1, p) % p
# one controlled basis for everything
K = np.array([[rng.randrange(p) for _ in range(H)] for _ in range(H)], dtype=np.int64)
if NESTED:
    K0 = np.array([[rng.randrange(p) for _ in range(h)] for _ in range(h)], dtype=np.int64)
    T2 = np.zeros((H, H), dtype=np.int64)
    for be in range(h):
        J = np.array([[rng.randrange(p) for _ in range(h)] for _ in range(h)], dtype=np.int64)
        for al in range(h):
            for al2 in range(h): T2[al*h+be, al2*h+be] = J[al, al2]
    K = mm(T2, np.kron(np.eye(h, dtype=np.int64), K0))
Gs = [np.array([[rng.randrange(p) for _ in range(h)] for _ in range(h)], dtype=np.int64) for _ in range(H)]
Tm = np.zeros((m, m), dtype=np.int64); Ti = np.zeros((m, m), dtype=np.int64)
for i in range(H):
    gi = inv_mod(Gs[i])
    for a in range(h):
        for b in range(h): Tm[a*H+i, b*H+i] = Gs[i][a, b]; Ti[a*H+i, b*H+i] = gi[a, b]
S = mm(Tm, np.kron(IF, K)); Si = mm(np.kron(IF, inv_mod(K)), Ti); assert (mm(S, Si) == I).all()
if MUT == 'noS': S, Si = I.copy(), I.copy()          # mutant: no controlled basis
if MUT == 'tensorS':                                   # mutant: G_i all equal (plain tensor basis G (x) K)
    S = np.kron(Gs[0], K) % p; Si = np.kron(inv_mod(Gs[0]), inv_mod(K)) % p
def classes():
    while True:
        A_, C_ = rng.sample(sets, 2)
        if len(set(A_) & set(C_)) == c0: break
    B_ = rng.choice(sets)
    q = np.kron(vec(B_), vec(C_)) % p
    Pq = proj_line(q, GG); PU = np.kron(IF, proj_line(vec(A_), G)); Pt = proj_line(vec(B_), G)
    if MUT != 'coord': assert not mm(Pq, PU).any()
    join = (I - np.kron(IF, Pq) - np.kron(Pt, PU)) % p
    t = vec(rng.choice(sets)); q = np.kron(vec(rng.choice(sets)), vec(rng.choice(sets))) % p
    d3 = np.kron((IF - proj_line(t, G)) % p, (IV - proj_line(q, GG)) % p) % p
    t3, t1, l = (vec(rng.choice(sets)) for _ in range(3))
    PB = (IF - proj_line(t1, G)) % p; Pl = (IF - proj_line(l, G)) % p
    d2 = np.kron(proj_line(t3, G), np.kron(PB, Pl) % p) % p            # B (x) l^perp (x) Q, third factor slow
    t3, t1 = vec(rng.choice(sets)), vec(rng.choice(sets))
    exitsf = (I - np.kron(proj_line(t3, G), np.kron(proj_line(t1, G), IF) % p) % p) % p   # I - Pi_t (x) Pi_X
    d = {
     'join(26880)':  (join,  m-2*h, [(i, i) for i in range(2*h, m-2*h)], 2*h),
     'data3(25142+842)': (d3, (h-1)*(H-1), [(i, m-H+i) for i in range(r, H-r)] + [(i, i) for i in range(H+r, m-H-r)], 3*r),
     'data2(782)':   (d2,   (h-1)**2, [(i, m-H+i) for i in range(2*h-1-(MUT=='blk+1'), H-2*h+1)], 2*h-1-(MUT=='blk+1')),
     'sfexit(26940)':(exitsf, m-h, [(i, i) for i in range(h, m-h)], h)}
    if NESTED or '--claim-nested' in sys.argv:   # PR 16 claim: corner pivots form an order-preserving block rows [0,h) -> cols [m-h,m), 0 singletons
        d['sfexit_nested(32,32704)'] = (exitsf, m-h, [(b, m-h+b) for b in range(h)] + [(i, i) for i in range(h, m-h)], 0)
    return d
res = {}; first_fail = None
for it in range(n_inst):
    for name, (A, rank, blk, nsing) in classes().items():
        assert (mm(A, A) == A).all(), name
        for tr, B in (('', A), ('^T', A.T.copy())):
            P = mm(mm(S, B), Si); piv = factor(P); sp = set(piv)
            ok = len(piv) == rank and set(blk) <= sp and len(sp - set(blk)) == nsing
            key = name + tr; res.setdefault(key, [0, 0]); res[key][0] += ok; res[key][1] += 1
            if not ok and first_fail is None:
                first_fail = (key, it, len(piv), rank, len(set(blk) - sp), len(sp - set(blk)), nsing)
allok = all(a == b for a, b in res.values())
print(f'h={h} m={m} k={k} seed={seed} family={"nested" if NESTED else "controlled"} mut={MUT or "none"}: passed/total {res}')
if first_fail: print('first failure (class, inst, rank found, rank expected, missing block pivots, extra pivots, expected singletons):', first_fail)
print('ALL PASS' if allok else 'SOME FAIL')
