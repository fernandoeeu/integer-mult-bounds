"""Negative controls for the PR 4 head checks (each must be rejected)."""
import sys
from fractions import Fraction
from circuit import Roles
import pr4new, scalar, flevel

h = int(sys.argv[1]) if len(sys.argv) > 1 else 8
res = {}

# 1. flip the sign of the E_i coefficient in the first pass: map must fail
orig = pr4new.scatter_passes
def flipped(h_, S, retain_last=False):
    ps = orig(h_, S)
    ps[0] = {k: (-c if k != ('tot', '*') else c) for k, c in ps[0].items()}
    return ps
pr4new.scatter_passes = flipped
C = pr4new.build(h)
ok, fails, _ = pr4new.check_map(C)
res['flip_Ei_sign: map rejected'] = not ok
M = pr4new.Motif(C, Roles(C))
s = scalar.single_invocation(M)
res['flip_Ei_sign: scalar rejected'] = not s['forward']['target']
pr4new.scatter_passes = orig

# 2. unsplit coefficient -(h-5)/2 in one pass: map exact but magnitude premise violated
def unsplit(h_, S, retain_last=False):
    ps = orig(h_, S)
    tot = {}
    for p in ps:
        for k, c in p.items():
            tot[k] = tot.get(k, 0) + c
    return [tot]
pr4new.scatter_passes = unsplit
C = pr4new.build(h)
ok, fails, maxc = pr4new.check_map(C)
res['unsplit: map still exact'] = ok
res['unsplit: max |coeff| > 1 detected'] = maxc > 1
pr4new.scatter_passes = orig

# 3. totals not retained (E_i, C_* missing): construction cannot run
C = pr4new.build(h, retain=False)
try:
    pr4new.check_map(C)
    res['no retention: rejected'] = False
except KeyError:
    res['no retention: rejected'] = True

# 4. frame variants
for var in ('J_before_R', 'reverse_uncomplemented'):
    C = pr4new.build(h); R = Roles(C)
    rec = lambda C_, R_, reverse=False, var=var: pr4new.invocation(C_, R_, reverse, var)
    out = flevel.run(C, R, rec, pr4new.label_space, verbose=False)
    bad = any(r['fails'] or r['loss'] != (h - 1) ** 2 + h for r in out.values())
    res['frame variant %s rejected' % var] = bad

for k, v in res.items():
    print(k, v)
print('CONTROLS', 'PASS' if all(res.values()) else 'FAIL')
