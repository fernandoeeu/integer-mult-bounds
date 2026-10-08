"""Mod-p screen (p = 2^24-3) of the controlled-basis corner conditions at larger h:
h=5,6 (k=3-subset labels, <S,T>=|S&T|-2) and h=8 (genuine five-subsets,
form I-(2/25)J, |A & piA| = 2).  One S = T(I(x)K) per h; for every instance
and its transpose: idempotent, rank, corner nonsingular, A2 corner diagonal.
Nonsingular mod p implies nonsingular over Q (entries are p-integral)."""
import sys, random, itertools, numpy as np
p = 16777213
def inv_mod(A):
    n = len(A); M = np.concatenate([A % p, np.eye(n, dtype=np.int64)], 1)
    for c in range(n):
        r = next(i for i in range(c, n) if M[i, c])
        M[[c, r]] = M[[r, c]]; M[c] = M[c] * pow(int(M[c, c]), -1, p) % p
        f = M[:, c].copy(); f[c] = 0
        M = (M - np.outer(f, M[c]) % p) % p
    return M[:, n:]
def rank_mod(A):
    M = A.copy() % p; r = 0; n, k = M.shape
    for c in range(k):
        piv = next((i for i in range(r, n) if M[i, c]), None)
        if piv is None: continue
        M[[r, piv]] = M[[piv, r]]; M[r] = M[r] * pow(int(M[r, c]), -1, p) % p
        f = M[:, c].copy(); f[r] = 0
        M = (M - np.outer(f, M[r]) % p) % p; r += 1
    return r
mm = lambda A, B: (A @ B) % p
def fr(a, b): return a * pow(b, -1, p) % p
def proj_line(t, G):
    Gt = mm(G, t.reshape(-1, 1)).ravel(); n = int(t @ Gt % p)
    return np.outer(t, Gt) % p * pow(n, -1, p) % p
def run(h, k, c0, rng, n_each=4):
    H = h*h; m = h*H
    alpha = fr(c0, k*k); G = (np.eye(h, dtype=np.int64) - alpha) % p; GG = np.kron(G, G) % p
    sets = list(itertools.combinations(range(h), k))
    vec = lambda S: np.array([1 if i in S else 0 for i in range(h)], dtype=np.int64)
    IF, IV, I = np.eye(h, dtype=np.int64), np.eye(H, dtype=np.int64), np.eye(m, dtype=np.int64)
    K = np.array([[rng.randrange(p) for _ in range(H)] for _ in range(H)], dtype=np.int64)
    Gs = [np.array([[rng.randrange(p) for _ in range(h)] for _ in range(h)], dtype=np.int64) for _ in range(H)]
    Tm = np.zeros((m, m), dtype=np.int64); Ti = np.zeros((m, m), dtype=np.int64)
    for i in range(H):
        gi = inv_mod(Gs[i])
        for a in range(h):
            for b in range(h): Tm[a*H+i, b*H+i] = Gs[i][a, b]; Ti[a*H+i, b*H+i] = gi[a, b]
    S = mm(Tm, np.kron(IF, K) % p); Si = mm(np.kron(IF, inv_mod(K)) % p, Ti)
    assert (mm(S, Si) == I).all()
    res = {'A1': [0, 0], 'A2': [0, 0], 'A3': [0, 0]}
    for _ in range(n_each):
        while True:
            A_, C_ = rng.sample(sets, 2)
            if len(set(A_) & set(C_)) == c0: break
        B_ = rng.choice(sets); tA, tC, tB = vec(A_), vec(C_), vec(B_)
        q = np.kron(tB, tC) % p
        Pq = proj_line(q, GG); PU = np.kron(IF, proj_line(tA, G)) % p; Pt = proj_line(tB, G)
        assert not mm(Pq, PU).any()
        A1 = (I - np.kron(IF, Pq) - np.kron(Pt, PU)) % p
        t = vec(rng.choice(sets)); A2 = np.kron((IF - proj_line(t, G)) % p, IV) % p
        t = vec(rng.choice(sets)); q = np.kron(vec(rng.choice(sets)), vec(rng.choice(sets))) % p
        A3 = np.kron((IF - proj_line(t, G)) % p, (IV - proj_line(q, GG)) % p) % p
        for name, A, a in (('A1', A1, m-2*h), ('A2', A2, m-H), ('A3', A3, (H-1)*(h-1))):
            for B in (A, A.T.copy()):
                P = mm(mm(S, B), Si); r = m - a
                ok = (mm(P, P) == P).all() and rank_mod(P) == a and rank_mod(P[:r, m-r:]) == r
                if name == 'A2':
                    cr = P[:r, m-r:]; ok &= not (cr - np.diag(np.diag(cr))).any() and np.diag(cr).all()
                res[name][0] += ok; res[name][1] += 1
    return res
rng = random.Random(11); allok = True
for h, k, c0 in ((5, 3, 2), (6, 3, 2), (8, 5, 2)):
    r = run(h, k, c0, rng, n_each=3 if h == 8 else 4)
    ok = all(a == b for a, b in r.values()); allok &= ok
    print(('PASS ' if ok else 'FAIL ') + f'h={h} m={h**3}: corner/idempotent/rank/A2-diagonal conditions met (passed/total per class) {r}'); sys.stdout.flush()
print('ALL PASS' if allok else 'SOME FAIL')
