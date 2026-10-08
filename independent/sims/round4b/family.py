"""Structured projector classes of notes/controlled-projector-basis.tex at
small h, from five-subset style rational labels with form G = I - alpha J,
and the controlled basis S = T (I_F (x) K)."""
from fractions import Fraction as Q
import random, itertools
from lin import *

def gform(h, alpha): return [[Q(int(i == j)) - alpha for j in range(h)] for i in range(h)]
def proj_line(t, G):                     # orthogonal projector onto <t> wrt G
    Gt = [sum(G[i][j]*t[j] for j in range(len(t))) for i in range(len(t))]
    n = sum(a*b for a, b in zip(t, Gt)); assert n != 0
    return [[t[i]*Gt[j]/n for j in range(len(t))] for i in range(len(t))]

def subset_vecs(h, k):
    return [[Q(1) if i in S else Q(0) for i in range(h)] for S in itertools.combinations(range(h), k)]

def instances(h, rng, n_each=4):
    """returns list of (class, matrix A, chain of frames) ; labels use k-subsets,
    k = (h+1)//2 with alpha chosen so <t_S,t_T> = |S cap T| - c0."""
    k, c0 = (2, 1) if h == 3 else (3, 2)
    alpha = Q(c0, k*k)                   # <t_S,t_T> = |S&T| - c0
    G = gform(h, alpha); GG = kron(G, G)
    vecs = subset_vecs(h, k); sets = list(itertools.combinations(range(h), k))
    H = h*h; IF = eye(h); IV = eye(H); I = eye(h*H)
    out = []
    pairs = [(a, b) for a in range(len(sets)) for b in range(len(sets)) if len(set(sets[a]) & set(sets[b])) == c0]
    for _ in range(n_each):
        # class 1: I - I_F (x) Pi_q - Pi_t (x) Pi_U ; q = t_B (x) t_piA, U = F (x) <t_A>, t = t_B
        A, C = rng.choice(pairs); B = rng.randrange(len(vecs))
        tB, tA, tC = vecs[B], vecs[A], vecs[C]
        q = [x*y for x in tB for y in tC]
        Pq = proj_line(q, GG); PU = kron(IF, proj_line(tA, G)); Pt = proj_line(tB, G)
        assert mul(Pq, PU) == zeros(H) and mul(PU, Pq) == zeros(H)
        Psmall = kron(Pt, PU); Pbig = add(I, kron(IF, Pq), -1)
        A1 = add(Pbig, Psmall, -1)
        out.append(('A1', A1, [zeros(h*H), Psmall, Pbig, I]))
        # class 2: (I_F - Pi_t) (x) I_V : from final frame Pi_t (x) I_V to I
        t = vecs[rng.randrange(len(vecs))]; Pt = proj_line(t, G)
        A2 = kron(add(IF, Pt, -1), IV)
        out.append(('A2', A2, [zeros(h*H), kron(Pt, IV), I]))
        # class 3: (I_F - Pi_t) (x) (I_V - Pi_q), q = t_a (x) t_b
        t = vecs[rng.randrange(len(vecs))]; Pt = proj_line(t, G)
        qa, qb = vecs[rng.randrange(len(vecs))], vecs[rng.randrange(len(vecs))]
        q = [x*y for x in qa for y in qb]
        if sum(a*b for a, b in zip(q, [sum(GG[i][j]*q[j] for j in range(H)) for i in range(H)])) == 0: continue
        Pq = proj_line(q, GG)
        A3 = kron(add(IF, Pt, -1), add(IV, Pq, -1))
        Plow = add(I, A3, -1)
        out.append(('A3', A3, [zeros(h*H), Plow, I]))
    return out, G

def controlled_S(h, rng, lo=-50, hi=50):
    H = h*h
    while True:
        K = [[Q(rng.randint(lo, hi)) for _ in range(H)] for _ in range(H)]
        if det_nonzero(K): break
    Gs = []
    for i in range(H):
        while True:
            g = [[Q(rng.randint(lo, hi)) for _ in range(h)] for _ in range(h)]
            if det_nonzero(g): Gs.append(g); break
    m = h*H
    Tm = zeros(m)
    for a in range(h):
        for b in range(h):
            for i in range(H): Tm[a*H+i][b*H+i] = Gs[i][a][b]
    S = mul(Tm, kron(eye(h), K))
    return S, inv(S)
