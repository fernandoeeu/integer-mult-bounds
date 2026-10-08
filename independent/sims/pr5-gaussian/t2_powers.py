"""T2: rigorous check of Lemma correction-powers and Corollary neumann-count,
plus the cited facts ||E|| < 2.01 e^{-pi a^2 theta/2} < 2^{-a^2 theta}, ||E|| < 0.42
(used by the revised interface under the weaker hypothesis a^2 theta >= 1).

E has nonnegative entries, so ||E^n||_inf = max_l (E^n 1)_l exactly; we iterate
v <- E v in Arb ball arithmetic. PASS means certified upper(||E^n||) < lower(bound).
A counterexample would need certified lower(||E^n||) > upper(bound).

usage: t2_powers.py SMAX ALPHAS NMAX PMAX [extra s,t pairs...]
"""
import sys
from fractions import Fraction as Fr
from math import ceil
from common import *

setprec(320)
SMAX = int(sys.argv[1]); ALPHAS = [int(a) for a in sys.argv[2].split(',')]
NMAX = int(sys.argv[3]); PMAX = int(sys.argv[4])
extra = [tuple(map(int, x.split(','))) for x in sys.argv[5:]]

pi = arb.pi()
pairs = admissible_pairs(SMAX) + extra  # 0 < theta < 1
cnt = dict(lemma=0, lemma_fail=0, lemma_undec=0, cited=0, cited_fail=0, cor=0, cor_fail=0, cor_undec=0)
worst_slack = None   # min over all of log2(bound) - log2(||E^n||)
worst_cited = None
cited_fail_list = []

for (s, t) in pairs:
    sig = Fr(t, s); th = sig - 1
    for al in ALPHAS:
        a2 = al * al
        Erows = E_matrix(s, t, al, H=8)
        M = arb_mat(Erows)
        v = arb_mat([[1] for _ in range(s)])
        burn = (pi * a2 * (1 / (4 * A(th)) + arb(1) / 2)).exp()
        rate = arb("2.01") * (-pi * a2 * A(sig)).exp()
        need_n = NMAX
        # corollary range: alpha^2 theta >= 1
        corok = a2 * th >= 1
        nmax_cor = 0
        if corok:
            for p in range(1, PMAX + 1):
                n1 = -(-p * th.denominator // (a2 * th.numerator))  # ceil(p/(a^2 theta))
                v2 = Fr(p + 1, 4 * a2) + 1 / th
                n2 = -(-v2.numerator // v2.denominator)
                nmax_cor = max(nmax_cor, min(n1, n2))
        norms = [None]
        for n in range(1, max(need_n, nmax_cor) + 1):
            v = M * v
            nrm = max((v[i, 0] for i in range(s)), key=lambda z: z.upper())
            # rigorous max: use upper of each entry for pass, lower for fail
            up = max(v[i, 0].upper() for i in range(s))
            lo = max(v[i, 0].lower() for i in range(s))
            norms.append((lo, up))
            if n <= NMAX:
                bound = burn * rate ** n
                cnt['lemma'] += 1
                if up < bound.lower():
                    sl = lg2(bound.lower()) - lg2(up)
                    if worst_slack is None or sl.upper() < worst_slack[0]:
                        worst_slack = (float(sl.mid()), s, t, al, n)
                elif lo > bound.upper():
                    cnt['lemma_fail'] += 1
                    print(f"LEMMA FAIL s={s} t={t} alpha={al} n={n} ||E^n||>={lo} bound={bound}")
                else:
                    cnt['lemma_undec'] += 1
        # cited facts on ||E|| when a^2 theta >= 1
        lo1, up1 = norms[1]
        if corok:
            cnt['cited'] += 1
            c1 = arb("2.01") * (-pi * a2 * A(th) / 2).exp()
            c2 = arb(2) ** (-A(a2 * th))
            ok = (up1 < c1.lower()) and (c1.upper() < c2.lower()) and (up1 < arb("0.42")) and (up1 < arb(1) / 2)
            r = float((up1 / c1.lower()).mid())
            if worst_cited is None or r > worst_cited[0]:
                worst_cited = (r, s, t, al)
            if not ok:
                cnt['cited_fail'] += 1
                cited_fail_list.append((s, t, al, float(up1.mid()), float(c1.mid())))
            # corollary for p = 1..PMAX
            for p in range(1, PMAX + 1):
                n1 = -(-p * th.denominator // (a2 * th.numerator))
                v2 = Fr(p + 1, 4 * a2) + 1 / th
                n2 = -(-v2.numerator // v2.denominator)
                n = min(n1, n2)
                cnt['cor'] += 1
                lo, up = norms[n]
                if n > p:
                    cnt['cor_fail'] += 1; print(f"COR FAIL n>p s={s} t={t} a={al} p={p} n={n}")
                if up < arb(2) ** (-p):
                    pass
                elif lo > arb(2) ** (-p):
                    cnt['cor_fail'] += 1
                    print(f"COR FAIL s={s} t={t} a={al} p={p} n={n} ||E^n||>={lo} > 2^-p")
                else:
                    cnt['cor_undec'] += 1
    sys.stdout.flush()

print("pairs:", len(pairs), "alphas:", ALPHAS, "NMAX:", NMAX, "PMAX:", PMAX)
print("counts:", cnt)
print("tightest lemma instance (log2 slack, s, t, alpha, n):", worst_slack)
print("largest ||E|| / (2.01 e^{-pi a^2 th/2}) over a^2 th>=1 (ratio, s,t,alpha):", worst_cited)
if cited_fail_list:
    print("cited-fact failures (first 20):", cited_fail_list[:20])
bad = cnt['lemma_fail'] + cnt['cor_fail'] + cnt['cited_fail']
print("RESULT:", "FAIL" if bad else ("PASS" if cnt['lemma_undec'] + cnt['cor_undec'] == 0 else "UNDECIDED-SOME"))
sys.exit(1 if bad else 0)
