"""Finite checks of projector-batching.tex and controlled-projector-basis.tex:
(i) for a rational idempotent (or nonzero multiple) of rank a>m/2 with
invertible first-r-row/last-r-column corner, the upstream lower-lower
elimination has r corner pivots then the contiguous diagonal block on M;
(ii) one controlled S = T(I(x)K) meets all three corner conditions for every
structured instance (and transposes, negatives) at small h, A2 corner
diagonal and pivots matched in physical order; (iii) negative controls."""
import sys, random, time
from fractions import Fraction as Q
from lin import *
from family import instances, controlled_S
OK = True
def check(n, c, x=''):
    global OK; OK &= bool(c); print(('PASS ' if c else 'FAIL ') + n + (' ' + str(x) if x != '' else '')); sys.stdout.flush()

def rand_idem(m, a, rng):
    while True:
        X = [[Q(rng.randint(-2, 2)) for _ in range(m)] for _ in range(m)]
        if det_nonzero(X): break
    D = zeros(m)
    for i in range(a): D[i][i] = Q(1)
    return mul(mul(X, D), inv(X))

def test_matrix(P, a, sign=1, want_matched=False):
    m = len(P); r = m - a
    P2 = mul(P, P)
    idem = P2 == scal(Q(sign), P)
    corner = [row[m-r:] for row in P[:r]]
    cinv = det_nonzero(corner)
    E1, Pi, E2, piv = lower_lower(P)
    fact = mul(mul(E1, Pi), E2) == P
    prof, matched = classify_pivots(piv, m, a)
    return dict(idem=idem, rank=rank(P) == a, corner=cinv, fact=fact, profile=prof, matched=matched)

rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
t0 = time.time()
print('== (i) random rational idempotents, random full GL conjugation, edge cases')
cnt = 0; bad = []
for m in range(3, 10):
    for a in range(m//2 + 1, m):
        for trial in range(6):
            P = rand_idem(m, a, rng)
            for sign in (1, -1, 3):
                Ps = scal(Q(sign), P)
                res = test_matrix(Ps, a, sign if sign != 3 else 3)
                if not res['corner']:
                    continue            # lemma hypothesis not met: skip (count below)
                cnt += 1
                if not (res['rank'] and res['fact'] and res['profile']): bad.append((m, a, sign, res))
check(f'random idempotents with invertible corner: profile = r corner + diagonal middle ({cnt} cases, m=3..9, a=floor(m/2)+1..m-1, t=1 included)', not bad, bad[:2])

print('== negative control: non-idempotent rank-a matrices with invertible corner')
viol = 0; tot = 0
for m in (5, 6, 7):
    for a in range(m//2+1, m):
        for trial in range(5):
            X = [[Q(rng.randint(-2, 2)) for _ in range(a)] for _ in range(m)]
            Y = [[Q(rng.randint(-2, 2)) for _ in range(m)] for _ in range(a)]
            A = mul(X, Y)
            if rank(A) != a or not det_nonzero([row[m-(m-a):] for row in A[:m-a]]): continue
            tot += 1
            _, _, _, piv = lower_lower(A)
            if not classify_pivots(piv, m, a)[0]: viol += 1
check(f'control: generic non-idempotents break the diagonal-middle profile in {viol}/{tot}', viol > 0 and viol >= tot//2)

for h in [int(x) for x in (sys.argv[2] if len(sys.argv) > 2 else '3,4').split(',')]:
    print(f'== (ii) structured classes h={h}, m={h**3}, one controlled S for all')
    inst, G = instances(h, rng, n_each=3 if h > 3 else 5)
    S, Si = controlled_S(h, rng)
    m = h**3; H = h*h
    allok = True; ncase = 0
    for cls, A, chain in inst:
        a = rank(A)
        exp_a = {'A1': m-2*h, 'A2': m-H, 'A3': (H-1)*(h-1)}[cls]
        check(f'  {cls} rank {a} = {exp_a}', a == exp_a)
        for variant in ('P', '-P', 'P^T'):
            B = A if variant == 'P' else (scal(Q(-1), A) if variant == '-P' else T(A))
            sign = -1 if variant == '-P' else 1
            Pc = mul(mul(S, B), Si)
            res = test_matrix(Pc, a, sign)
            ncase += 1
            good = all(res.values()) if cls == 'A2' else all(v for k, v in res.items() if k != 'matched')
            if cls == 'A2':
                r = m - a
                cornr = [row[m-r:] for row in Pc[:r]]
                diag = all(cornr[i][j] == 0 for i in range(r) for j in range(r) if i != j) and all(cornr[i][i] != 0 for i in range(r))
                good &= diag
            if not good:
                allok = False; print('   FAIL detail', cls, variant, res)
            # unconjugated control: S = I
        print(f'   {cls}: {"ok" if allok else "BAD"} ({time.time()-t0:.0f}s)'); sys.stdout.flush()
    check(f'h={h}: all {ncase} structured cases meet corner conditions, idempotency, factorization and claimed pivot profile (A2: diagonal corner, matched order)', allok)
    # negative control: without conjugation (S=I) the corner conditions fail
    fails = 0
    for cls, A, chain in inst[:3]:
        a = rank(A); r = m - a
        if not det_nonzero([row[m-r:] for row in A[:r]]): fails += 1
    check(f'  control: unconjugated (S=I) corners singular for {fails}/3 classes (controlled basis needed)', fails >= 1)
print('ALL PASS' if OK else 'SOME FAIL', f'{time.time()-t0:.0f}s')
