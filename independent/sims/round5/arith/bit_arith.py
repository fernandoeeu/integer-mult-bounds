"""Independent exact recomputation of the bit-side rank accounting and moments of
PR 14 (h30 source frames + data corners), PR 15 (h30 stream producer + source frames)
and PR 16 (h32 nested), from the numbers stated in their notes.  Rank-sum identity,
singleton count, block widths derived from formulas, strict moment with our own
log upper bounds (verified by exp lower series), and negative controls (next savings
must fail; dropping a class's block changes S)."""
from fractions import Fraction as Q
from math import comb, log
import sys
ok = True
def chk(n, c, x=''):
    global ok; ok &= bool(c); print(('PASS ' if c else 'FAIL ') + n, x); sys.stdout.flush()
def exp_lower(l, K=60):
    s, t = Q(0), Q(1)
    for k in range(K): s += t; t = t * l / (k + 1)
    return s
L2 = Q(693147180560, 10**12); assert exp_lower(L2) > 2
def log_up(x):
    k = 0
    while x > 2: x /= 2; k += 1
    l = Q(log(float(x))).limit_denominator(10**13) + Q(1, 10**12)
    assert exp_lower(l) > x
    return k*L2 + l
def moment(S, blocks, W, m, a):
    terms = [(Q(S, W*m), Q(m))] + [(Q(c*t, W*m), Q(m, t)) for c, t in blocks]
    return sum(w / (1 - a*log_up(x)) for w, x in terms), sum(w for w, _ in terms)
def network(h, R):
    v = comb(h, 5); m = h**3; N = v**3; W = 2*v*v*(v+R); L = 3*v*v*comb(h, 2)*(h-2); s = W*m - N + 2*L
    return v, m, N, W, s, v*v*R
# ---------------- PR 14
h = 30; H = h*h; v, m, N, W, s, B = network(h, 17515487)
blocks = [(B, m-4*h), (B, m-2*h), (2*N, m-2*H-2*h+2), (2*N, H-2*h+2), (2*N, H-4*h+2)]
chk('PR14 widths 26880,26940,25142,842,782', [t for _, t in blocks] == [26880, 26940, 25142, 842, 782])
S = s - sum(c*t for c, t in blocks); chk('PR14 singleton count', S == 65379670780393117512, S)
# singleton count from per-edge profiles: join 2h, exit h, data3 3(h-1), data2 2h-1, every other rank unit 1
mu, tot = moment(S, blocks, W, m, Q(1816, 10**9)); chk('PR14 weights = 1-eta', tot == 1 - Q(N - 2*(3*v*v*comb(h,2)*(h-2)), W*m))
chk('PR14 bit moment < 1 at 1816e-9', mu < 1, float(1-mu))
mu2, _ = moment(S, blocks, W, m, Q(1821, 10**9)); chk('PR14 control: 1821e-9 fails', mu2 >= 1, float(1-mu2))
mu3, _ = moment(S + 2*N*842, blocks[:3] + blocks[4:], W, m, Q(1816, 10**9)); chk('PR14 control: without 842 block fails', mu3 >= 1, float(1-mu3))
chk('PR14 complex leaf (1-beta)a_c > a_b', (1 - Q(1, 1000))*Q(18179, 10**10) > Q(1816, 10**9))
# ---------------- PR 15
v, m, N, W, s, B = network(30, 13056812)
blocks = [(B, m-4*h), (2*N, m-2*H-2*h+2), (B, m-2*h)]
S = s - sum(c*t for c, t in blocks)
a15 = Q(2153359, 10**12)
mu, _ = moment(S, blocks, W, m, a15); chk('PR15 bit moment < 1 at 2153359e-12', mu < 1, float(1-mu))
mu2, _ = moment(S, blocks, W, m, a15 + Q(5, 10**12)); chk('PR15 control: +5e-12 fails (note: next grid point fails)', mu2 >= 1, float(1-mu2))
mu4, _ = moment(*(lambda R: (network(30, R)[4] - sum(c*t for c, t in [(network(30,R)[5], m-4*h), (2*N, m-2*H-2*h+2), (network(30,R)[5], m-2*h)]),
     [(network(30,R)[5], m-4*h), (2*N, m-2*H-2*h+2), (network(30,R)[5], m-2*h)], network(30,R)[3], m, a15))(17515487))
chk('PR15 control: PR12 role count 17515487 fails at same saving', mu4 >= 1, float(1-mu4))
# ---------------- PR 16
h = 32; H = h*h; v, m, N, W, s, B = network(h, 25224960)
chk('PR16 W, s, B', (W, s, B) == (2062192473897500672, 67573918438923423744000, 1022929978317864960), (W, s, B))
blocks = [(B, m-4*h), (B, h), (B, m-2*h), (2*N, H-4*h+2), (2*N, H-2*(h-1)), (2*N, m-2*H-2*(h-1))]
chk('PR16 widths', [t for _, t in blocks] == [32640, 32, 32704, 898, 962, 30658])
S = s - sum(c*t for c, t in blocks); chk('PR16 singleton count', S == 167747380096422805504, S)
mu, _ = moment(S, blocks, W, m, Q(49, 25000000)); chk('PR16 bit moment < 1 - 3e-10 at 49/25e6', mu < 1 - Q(3, 10**10), float(1-mu))
mu2, _ = moment(S, blocks, W, m, Q(50, 25000000)); chk('PR16 control: 2e-6 fails', mu2 >= 1, float(1-mu2))
mu5, _ = moment(S + B*h, [b for b in blocks if b[1] != h], W, m, Q(49, 25000000)); chk('PR16 control: exit corner as h singletons (non-nested) fails', mu5 >= 1, float(1-mu5))
chk('PR16 eta', Q(W*m - s, W*m) == Q(3503, 52073136128))
print('ALL PASS' if ok else 'SOME FAIL')
