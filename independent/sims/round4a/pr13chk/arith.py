"""Independent exact recomputation of PR 13's numbers (source-frame-bit.tex,
source-frame-complex.tex, source-frame-assembly.tex), from the formulas in
the notes only.  Fractions throughout; exp lower bounds by positive Taylor
partial sums (so 'exp(l) > x' is proved exactly)."""
from fractions import Fraction as Q
from math import comb, factorial
import json, sys

ok = True
def chk(name, cond, extra=''):
    global ok
    ok &= bool(cond)
    print(('PASS ' if cond else 'FAIL ') + name, extra)

def exp_lower(l, K=60):
    s, t = Q(0), Q(1)
    for k in range(K):
        s += t
        t = t * l / (k + 1)
    return s

def log_upper_ok(x, l):          # log(x) < l  <=>  exp(l) > x
    return exp_lower(Q(l)) > x

# ---------------------------------------------------------------- bit side
h = 28; v = comb(h, 5); m = h ** 3; H = h * h; R = 11840940; N = v ** 3
W = 2 * v * v * (v + R); L = 3 * v * v * comb(h, 2) * (h - 2); s = W * m - N + 2 * L
B = v * v * R
chk('B value', B == 114371146876896000, B)
eta = Q(W * m - s, W * m)
chk('eta = 39/520019360', eta == Q(39, 520019360), eta)
# PR 10 three classes: join a=m-2h, stage-2 sink a=m-h^2, stage-3 data d3=(h^2-1)(h-1)
d3 = (h * h - 1) * (h - 1)
chk('d3 = 21141', d3 == 21141)
k_join, k_sink, k_data = 2 * (m - 2 * h) - m, 2 * (m - H) - m, 2 * d3 - m
chk('batched widths 21840/20384/20330', (k_join, k_sink, k_data) == (21840, 20384, 20330))
S0 = s - B * k_join - B * k_sink - 2 * N * k_data
S1 = S0 - B * H
chk('S_1 (controlled) matches note', S1 == 105555640096680883200, S1)
# per-role rank bookkeeping for a stage-two auxiliary role (old vs new end edges)
old_ends = (H - h) + (m - H)      # entrance from 0 to D_0 ; exit D_1 -> I
new_ends = 0 + (m - h)            # entrance P_D0 -> D_0 ; exit D_1 -> I + P_D0
chk('end-edge rank total unchanged per role', old_ends == new_ends, (old_ends, new_ends))
# new singleton count from scratch: every rank unit outside the three middle blocks
k_exit = m - 2 * h
S2 = s - B * k_join - 2 * N * k_data - B * k_exit
chk("S' from scratch = S_1 - B(h^2-2h) = note", S2 == S1 - B * (H - 2 * h) == 22293445170300595200, S2)
ratios = [Q(1, m), Q(k_join, m), Q(k_data, m), Q(k_exit, m)]
chk('ratios', ratios == [Q(1, 21952), Q(195, 196), Q(10165, 10976), Q(391, 392)])
w = [Q(S2, W * m), Q(B * k_join, W * m), Q(2 * N * k_data, W * m), Q(B * k_exit, W * m)]
chk('weights match note', w == [Q(2289741, 520019360), Q(12827685, 26000968), Q(20865, 2736944), Q(25721153, 52001936)], w)
chk('weights sum to 1-eta', sum(w) == 1 - eta)
ells = [Q(9997, 1000), Q(512, 10 ** 5), Q(768, 10 ** 4), Q(2555, 10 ** 6)]
for r, l in zip(ratios, ells):
    chk(f'log(1/{r}) < {l}', log_upper_ok(1 / r, l))
ab = Q(154, 10 ** 8)
up = sum(wi / (1 - ab * li) for wi, li in zip(w, ells))
gap = 1 - up
chk('bit moment < 1', up < 1)
chk('bit gap equals note fraction', gap == Q(9704597579224556535778749633448639054699, 20663392005574270637817582110595278287793980851574), float(gap))
chk('bit gap > 4.69e-10', gap > Q(469, 10 ** 12))
# sharper: largest a_b with this bound (bisection on rationals), for context
lo, hi = Q(0), Q(1, 10 ** 4)
for _ in range(60):
    mid = (lo + hi) / 2
    if sum(wi / (1 - mid * li) for wi, li in zip(w, ells)) < 1: lo = mid
    else: hi = mid
print('  max a_b certifiable with these log bounds ~', float(lo))
# negative control: PR 10's own numbers must give a smaller certifiable saving
w10 = [Q(S1, W * m), Q(B * k_join, W * m), Q(B * (m - 2 * H), W * m), Q(2 * N * k_data, W * m), Q(B * H, W * m)]
chk('control: PR10 controlled weights sum to 1-eta', sum(w10) == 1 - eta)
chk('control: a_b=154e-8 NOT certifiable for PR10 profile',
    sum(wi / (1 - ab * li) for wi, li in zip(w10, [ells[0], ells[1], Q(7411, 10**5), ells[2], Q(33323, 10000)])) >= 1)

# ------------------------------------------------------------ complex side
vc = comb(28, 3); Rc = 93838
Bc = vc * vc * (Rc + h + 1); Wc = 2 * vc * vc * (vc + Rc + h + 1); Lc = 3 * vc * vc * h * (h + 1)
sc = Wc * m - 2 * vc ** 3 + 2 * Lc
chk('complex B_c, W_c, s_c', (Bc, Wc, sc) == (1007397164592, 2085111546336, 45772350635112192))
a1, a2 = m - 2 * h, m - H
chk('2 v_c^3', 2 * vc ** 3 == 70317217152)
Sc = sc - Bc * (a1 + a2) - 2 * vc ** 3 * d3
chk("S_c' matches", Sc == 903222851311872, Sc)
etac = Q(Wc * m - sc, Wc * m)
chk('eta_c = 5/12693352', etac == Q(5, 12693352))
rc = [Q(1, m), Q(a1, m), Q(a2, m), Q(d3, m)]
chk('complex ratios', rc == [Q(1, 21952), Q(391, 392), Q(27, 28), Q(21141, 21952)])
wc = [Q(Sc, Wc * m), Q(Bc * a1, Wc * m), Q(Bc * a2, Wc * m), Q(2 * vc ** 3 * d3, Wc * m)]
chk('complex weights', wc == [Q(250477, 12693352), Q(12233999, 25386704), Q(844803, 1813336), Q(824499, 25386704)], wc)
chk('complex weights sum', sum(wc) == 1 - etac)
ellc = [Q(9997, 1000), Q(2555, 10 ** 6), Q(36368, 10 ** 6), Q(37644, 10 ** 6)]
for r, l in zip(rc, ellc):
    chk(f'log(1/{r}) < {l}', log_upper_ok(1 / r, l))
ac = Q(18, 10 ** 7)
upc = sum(wi / (1 - ac * li) for wi, li in zip(wc, ellc))
chk('complex moment < 1', upc < 1)
chk('complex gap equals note', 1 - upc == Q(12084702927461727916508294311187513281917509, 3098906698934144550424761963671962638378246719417509), float(1 - upc))
# guard
q = m + 6 * h
chk('q = 22120', q == 22120)
chk('2*d3 > q and all selected ranks > q/2', all(2 * a > q for a in (a1, a2, d3)))
chk('160000^5 < m^6', 160000 ** 5 < m ** 6)
t = Q(m - d3, m)
pm = Q(q - d3, 160000) + 1 - Q(6, 5) * t + Q(3, 25) * t * t / (1 - t)
chk('guard path moment value', pm == Q(372026142559, 386739360000), pm)
chk('guard < 999/1000', pm < Q(999, 1000))
chk('(q-d3)/160000 == 979/160000', Q(q - d3, 160000) == Q(979, 160000))
# binomial-series bound used: c_k for k>=2 positive and <= 3/25
rho = Q(6, 5); c = Q(1); cs = []
for k in range(1, 40):
    c = c * (rho - k + 1) / k
    cs.append(c * (-1) ** k)
chk('(1-t)^{6/5} series tail coeffs in (0,3/25] for k>=2', all(0 < x <= Q(3, 25) for x in cs[1:]))

# ----------------------------------------------------------- assembly
tau = 1 - ab; sigma = 1 - ac; eps = Q(499999, 10 ** 6); cc = Q(1); beta = Q(1, 1000)
delta = Q(1, 10 ** 10); zeta = Q(1, 10 ** 4); C1 = Q(11999, 10000)
lam = tau + Q(1, 10 ** 16); lamp = tau + Q(2, 10 ** 16); kappa = Q(7699, 10 ** 10)
chk('sigma < tau', sigma < tau)
chk('C1 = 6/5 - beta/5 + zeta', C1 == Q(6, 5) - beta / 5 + zeta)
chk('leaf exponent', sigma + beta * (1 - sigma) == 1 - Q(17982, 10 ** 10) and sigma + beta * (1 - sigma) < tau)
chk('1 - eps*C1', 1 - eps * C1 == Q(4000511999, 10 ** 10))
g = dict(g1=1 - eps * (1 + cc), g2=eps * cc * (1 - tau), g3=eps * (1 - lamp), g4=(1 - eps) * (1 - tau),
         g5=1 - delta - 2 * eps, g6=1 - delta - eps, g7=eps)
want = dict(g1=Q(1, 500000), g2=Q(38499923, 5 * 10 ** 13), g3=Q(3849992299500001, 5 * 10 ** 21),
            g4=Q(38500077, 5 * 10 ** 13), g5=Q(19999, 10 ** 10), g6=Q(5000009999, 10 ** 10), g7=Q(499999, 10 ** 6))
for k in g:
    chk('margin ' + k, g[k] == want[k], g[k])
G = min(g.values())
chk('min margin is g3', G == g['g3'])
chk('G - kappa', G - kappa == Q(492299500001, 5 * 10 ** 21), G - kappa)
chk('kappa > 2^-21', kappa > Q(1, 2 ** 21))
chk('lambda < 1 (tau + 2e-16 < 1)', lamp < 1)
print('ALL PASS' if ok else 'SOME FAIL')
sys.exit(0 if ok else 1)
