"""Independent recomputation of the finite counts and exact exponent
comparisons of PR 10 (62691e3) and PR 12 (35d31e3), from the notes only.
Rigorous: log upper bounds by atanh series with explicit remainder, exp upper
bound exp(y) <= 1/(1-y).  mpmath (80 digits) only for slack reporting."""
from fractions import Fraction as Q
from math import comb
import mpmath as mp
mp.mp.dps = 80
OK = True
def check(name, cond, extra=''):
    global OK
    OK &= bool(cond)
    print(('PASS ' if cond else 'FAIL ') + name + ('  ' + str(extra) if extra else ''))

def log_upper(x, terms=40):
    """rigorous rational upper bound for log(x), x>1 rational"""
    x = Q(x); k = 0
    while x > 2: x /= 2; k += 1
    z = (x - 1) / (x + 1); s = Q(0); zz = z
    for j in range(terms):
        s += zz / (2*j+1); zz *= z*z
    rem = zz / ((2*terms+1) * (1 - z*z))
    l2 = Q(0); z2 = Q(1, 3); zz = z2
    for j in range(terms):
        l2 += zz/(2*j+1); zz *= z2*z2
    l2 += zz/((2*terms+1)*(1-z2*z2))
    return 2*(s + rem) + k*2*l2

def moment_upper(weights_ratios, a):
    """sum w_i * ratio_i^(-a), ratio<=1 ; upper bound via exp(y)<=1/(1-y)"""
    up = Q(0)
    for w, r in weights_ratios:
        if r == 1: up += w; continue
        y = a * log_upper(1/r)
        assert 0 <= y < 1
        up += w / (1 - y)
    return up

def moment_mp(weights_ratios, a):
    return mp.fsum(mp.mpf(w.numerator)/w.denominator * mp.e**(mp.mpf(a.numerator)/a.denominator*mp.log(mp.mpf((1/r).numerator)/(1/r).denominator)) for w, r in weights_ratios)

def max_saving(weights_ratios):
    f = lambda a: moment_mp(weights_ratios, Q(a).limit_denominator(10**30)) - 1
    g = lambda a: mp.fsum(mp.mpf(w.numerator)/w.denominator*mp.e**(a*mp.log(mp.mpf((1/r).numerator)/(1/r).denominator)) for w, r in weights_ratios) - 1
    return mp.findroot(g, mp.mpf('1e-7'))

def bit(h, R, a_claim, S1_claim=None, eta_claim=None, gap_claim=None, tag=''):
    v = comb(h, 5); m = h**3; H = h*h; N = v**3
    W = 2*v*v*(v+R); L = 3*v*v*comb(h, 2)*(h-2); s = W*m - N + 2*L
    eta = Q(W*m - s, W*m)
    print(f'--- bit network {tag} h={h} v={v} m={m} R={R}')
    if eta_claim is not None: check(f'eta = {eta_claim}', eta == eta_claim, eta)
    B = v*v*R
    a1, a2, a3 = m-2*h, m-H, (H-1)*(h-1)
    check('rank formulas: data rank sum 2N*sum(d_j+h-1)+N = 2Nm-N',
          2*N*sum((h**(j-1)-1)*(h-1)+h-1 for j in (1, 2, 3)) + N == 2*N*m - N)
    check('three classes all exceed m/2', min(a1, a2, a3)*2 > m, (a1, a2, a3))
    k = [2*a - m for a in (a1, a2, a3)]
    print('   singleton pivots', [m-a for a in (a1, a2, a3)], 'middle widths', k)
    S0 = s - B*k[0] - B*k[1] - 2*N*k[2]
    S1 = S0 - B*H        # stage-2 corner now one block of H subfields
    if S1_claim is not None: check(f'S1 = {S1_claim}', S1 == S1_claim, S1)
    check('S1 > 0', S1 > 0)
    # direct singleton count: sum over classes of their singletons must be <= S1 bookkeeping
    wr = [(Q(S1, W*m), Q(1, m)), (Q(B*k[0], W*m), Q(k[0], m)), (Q(B*k[1], W*m), Q(k[1], m)),
          (Q(2*N*k[2], W*m), Q(k[2], m)), (Q(B*H, W*m), Q(H, m))]
    check('rank-mass weights sum to 1-eta (Psi(1) = s/(Wm))', sum(w for w, _ in wr) == 1 - eta)
    up = moment_upper(wr, a_claim)
    check(f'Psi(1-{a_claim}) rigorous upper < 1', up < 1, f'gap={float(1-up):.4e}')
    if gap_claim: check(f'gap > {gap_claim}', 1-up > gap_claim)
    mx = max_saving(wr)
    print(f'   max saving a with Psi(1-a)=1 (mpmath): {mp.nstr(mx, 12)}; claimed {float(a_claim):.6e}')
    # what unbatched would give
    mxu = max_saving([(1-eta, Q(1, m))])
    print(f'   unbatched max saving: {mp.nstr(mxu, 8)}')
    # Without controlled-basis corner (PR10 intermediate 177e-9)
    wr0 = [(Q(S0, W*m), Q(1, m))] + wr[1:4]
    print(f'   intermediate (no controlled corner) max saving: {mp.nstr(max_saving(wr0), 8)}')
    return wr, mx

def cplx():
    h = 28; v = comb(h, 3); m = h**3; R = 93838; aux = R+h+1
    B = v*v*aux; W = 2*v*v*(v+aux); L = 3*v*v*h*(h+1); s = W*m - 2*v**3 + 2*L
    print('--- complex network h=28')
    check('B_c = 1007397164592', B == 1007397164592)
    check('W_c = 2085111546336', W == 2085111546336)
    check('L_c = 26143580736', L == 26143580736)
    check('s_c = 45772350635112192', s == 45772350635112192)
    a1, a2 = m-2*h, m-h*h
    S = s - B*(a1+a2)
    check('S_c = 2389799139122304', S == 2389799139122304)
    eta = Q(W*m-s, W*m)
    check('eta_c = 5/12693352', eta == Q(5, 12693352))
    wr = [(Q(S, W*m), Q(1, m)), (Q(B*a1, W*m), Q(a1, m)), (Q(B*a2, W*m), Q(a2, m))]
    up = moment_upper(wr, Q(7, 10**7))
    check('Xi(1-7e-7) < 1', up < 1, f'gap={float(1-up):.4e}')
    print('   max complex saving', mp.nstr(max_saving(wr), 10))
    # path guard
    q = m + 6*h
    check('both bulk ranks > q/2 (=> at most one bulk edge per path)', 2*a1 > q and 2*a2 > q)
    rho = mp.mpf(6)/5
    vals = [q/mp.mpf(m)**rho, (q-a1)/mp.mpf(m)**rho + (mp.mpf(a1)/m)**rho, (q-a2)/mp.mpf(m)**rho + (mp.mpf(a2)/m)**rho]
    check('path moments < 999/1000', max(vals) < mp.mpf(999)/1000, [mp.nstr(x, 10) for x in vals])
    # rational: m^(6/5) > 160000 ; (1-t)^(6/5) <= 1 - 6t/5 + 3t^2/(25(1-t))
    check('160000^5 < m^6', 160000**5 < m**6)
    ups = [Q(q, 160000)]
    for a in (a1, a2):
        t = Q(m-a, m); ups.append(Q(q-a, 160000) + 1 - Q(6, 5)*t + Q(3, 25)*t*t/(1-t))
    check('rational path bounds 553/4000, 47817969/47897500, 1213697/1260000',
          ups == [Q(553, 4000), Q(47817969, 47897500), Q(1213697, 1260000)], ups)
    # Is "one path one bulk" also needed for 2 bulk in the time moment? no; but check what 2 bulk would give
    print('   (control) a path with two a2-bulk children would have moment', mp.nstr(2*(mp.mpf(a2)/m)**rho, 8))
    return wr

def assembly(tau_s, sig_s, eps, c, beta, delta, zeta, C1, lam_off, lamp_off, kappa, tag):
    print('--- assembly', tag)
    tau, sigma = 1 - tau_s, 1 - sig_s
    lam, lamp = tau + lam_off, tau + lamp_off
    rho = Q(6, 5)
    check('C1 = rho-(rho-1)beta+zeta', C1 == rho - (rho-1)*beta + zeta)
    check('1 - eps*C1 > 0', 1 - eps*C1 > 0, 1-eps*C1)
    check('sigma < tau', sigma < tau)
    check('leaf exponent sigma+beta(1-sigma) < lambda\'', sigma + beta*(1-sigma) < lamp)
    chi = tau + (1-beta)*max(sigma-tau, 0)
    check('max(tau,sigma,chi) < lambda < lambda\' < 1', max(tau, sigma, chi) < lam < lamp < 1)
    g = [1-eps*(1+c), eps*c*(1-tau), eps*(1-lamp), (1-eps)*(1-tau), 1-delta-2*eps, 1-delta-eps, eps]
    print('   margins', [str(x) for x in g])
    G = min(g)
    check(f'min margin {G} > kappa {kappa}', G > kappa, G - kappa)
    check('kappa > 2^-23', kappa > Q(1, 2**23), float(kappa)/2**-23)
    return g

if __name__ == '__main__':
    print('== PR 10 (h=28)')
    bit(28, 11840940, Q(246, 10**9), S1_claim=105555640096680883200, eta_claim=Q(39, 520019360), gap_claim=Q(476, 10**13), tag='PR10')
    cplx()
    g = assembly(Q(246, 10**9), Q(7, 10**7), Q(7999999, 16000000), Q(1), Q(1, 1000), Q(1, 10**10), Q(1, 10**4), Q(11999, 10000),
                 Q(1, 10**16), Q(2, 10**16), Q(6149999, 5*10**13), 'PR10')
    claimed = [Q(1, 8000000), Q(983999877, 8000000000000000), Q(9839998762000001, 80000000000000000000000), Q(984000123, 8000000000000000),
               Q(1249, 10000000000), Q(312500039, 625000000), Q(7999999, 16000000)]
    check('PR10 margin table values', g == claimed)
    check('PR10 G - kappa = 362000001/8e22', min(g) - Q(6149999, 5*10**13) == Q(362000001, 80000000000000000000000))
    print('== PR 12 (bit h=30, complex h=28)')
    bit(30, 17515487, Q(253, 10**9), S1_claim=373570603170925665960, eta_claim=Q(3857, 52973979000), gap_claim=Q(9, 10**12), tag='PR12')
    assembly(Q(253, 10**9), Q(7, 10**7), Q(49999993, 10**8), Q(1), Q(1, 1000), Q(1, 10**10), Q(1, 10**4), Q(11999, 10000),
             Q(1, 10**16), Q(2, 10**16), Q(12649, 10**11), 'PR12')
    print('== negative controls (must FAIL internally)')
    import io, contextlib
    for name, fn in [('bit saving 300e-9 at h=28', lambda: bit(28, 11840940, Q(300, 10**9))),
                     ('complex-like: kappa = min margin', lambda: assembly(Q(246, 10**9), Q(7, 10**7), Q(7999999, 16000000), Q(1), Q(1, 1000), Q(1, 10**10), Q(1, 10**4), Q(11999, 10000), Q(1, 10**16), Q(2, 10**16), Q(9839998762000001, 80000000000000000000000), 'ctl')),
                     ('inflated role count R*1.001 at h=28 fails S1 claim', lambda: bit(28, 11852781, Q(246, 10**9), S1_claim=105555640096680883200))]:
        save = OK; buf = io.StringIO()
        with contextlib.redirect_stdout(buf): fn()
        detected = 'FAIL' in buf.getvalue()
        OK = save
        print(('PASS ' if detected else 'FAIL ') + 'negative control detected: ' + name)
        OK &= detected
    print('ALL PASS' if OK else 'SOME FAIL')
