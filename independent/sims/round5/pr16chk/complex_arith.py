"""PR 16 nested-complex.tex: independent exact arithmetic from the note only:
histogram sum, global rank identity sum r H_r = s, max rank < m, path guard
moment (rho = 3/2), and the complex moment at a_c = 4e-6 using exact exp lower
bounds (log x < l  <=>  exp(l) > x).  Negative controls: a_c too large, guard with
q = m+6h but M = m (rank-m exception) must exceed theta."""
from fractions import Fraction as Q
from math import comb
ok = True
def chk(n, c, x=''):
    global ok; ok &= bool(c); print(('PASS ' if c else 'FAIL ') + n, x)
def exp_lower(l, K=40):
    s, t = Q(0), Q(1)
    for k in range(K): s += t; t = t * l / (k + 1)
    return s
h = 28; v = comb(h, 3); m = h**3; R = 93838; N = v**3; B = v*v*(R+h+1)
W = 2*v*v*(v+R+h+1); L = 3*v*v*h*(h+1); D = 2*N - 2*L; s = W*m - D
chk('B, W, D, s', (B, W, D, s) == (1007397164592, 2085111546336, 18030055680, 45772350635112192), (B, W, D, s))
c = {1:93912,2:23891,3:21224,4:31667,5:13552,6:9128,7:9240,8:10912,9:5656,10:8456,11:4284,12:7598,13:4872,14:7448,
     15:4536,16:7803,17:4228,18:8232,19:4872,20:7482,21:7224,22:5901,23:8400,24:11550,25:1512,26:5180,27:6552,28:87}
loc = sum(r*n for r, n in c.items())
chk('local sum r c_r = 2806804 = (2v+R+h+1)h-2v+2h(h+1)', loc == 2806804 == (2*v+R+h+1)*h - 2*v + 2*h*(h+1), loc)
Hh = {}
for r, n in c.items(): Hh[r] = Hh.get(r, 0) + 3*v*v*n
for r, n in ((m-2*h, B), (m-h*h, B), (h*h-h, B), ((h-1)**2, 2*N), ((h*h-1)*(h-1), 2*N)): Hh[r] = Hh.get(r, 0) + n
chk('global sum r H_r = s', sum(r*n for r, n in Hh.items()) == s)
M = max(Hh); chk('max rank M = 21896 < m', M == 21896 < m, M)
q = m + 6*h
def guard(Mx):
    t = Q(m - Mx, m); y = Q(q - Mx, m)
    # exact upper bounds: (1-t)^{3/2} <= 1 - 3t/2 + (3/8) t^2/(1-t);  y^{3/2} = y*sqrt(y) < y*s for rational s > sqrt(y)
    sq = Q(1, 9) if Mx == M else None
    if sq is None:
        import math; sq = Q(math.sqrt(float(y))).limit_denominator(10**9) + Q(1, 10**9)
    assert sq*sq >= y
    return (1 - Q(3, 2)*t + Q(3, 8)*t*t/(1-t)) + y*sq
g = guard(M)
chk('guard bound = 11005895/11035584 < 999/1000', g == Q(11005895, 11035584) and g < Q(999, 1000), float(g))
chk('sqrt(1/98) < 1/9', Q(1, 81) > Q(1, 98))
# complex moment
def log_up(x):
    k = 0
    while x > 2: x /= 2; k += 1
    # find rational l with exp(l) > x via upper series bound: refine on grid 1e-12
    import math
    l = Q(math.log(float(x))).limit_denominator(10**12) + Q(1, 10**11)
    assert exp_lower(l) > x
    l2 = Q(693147180560, 10**12); assert exp_lower(l2) > 2
    return k*l2 + l
def moment(a):
    tot = Q(0)
    for r, n in Hh.items():
        lr = log_up(Q(m, r)); assert a*lr < 1
        tot += Q(n*r, W*m) / (1 - a*lr)
    return tot + 0 # singleton term r=1 included in Hh (rank-1 edges): no separate singleton mass
chk('weights sum to 1 - D/(Wm)', sum(Q(n*r, W*m) for r, n in Hh.items()) == 1 - Q(D, W*m))
mo = moment(Q(4, 10**6)); chk('complex moment < 1 at a_c = 4e-6', mo < 1, float(1-mo))
mo2 = moment(Q(419, 10**8)); chk('complex moment < 1 at a_c = 419e-8 (note: also supported)', mo2 < 1, float(1-mo2))
mo3 = moment(Q(45, 10**7)); chk('control: a_c = 4.5e-6 NOT certified', mo3 >= 1, float(1-mo3))
chk('control: guard with a rank-m child (M=m) exceeds 999/1000', guard(m) > Q(999, 1000), float(guard(m)))
print('ALL PASS' if ok else 'SOME FAIL')
