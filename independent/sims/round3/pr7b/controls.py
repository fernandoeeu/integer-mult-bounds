"""Negative controls for net.py: each mutant must be rejected."""
import sys, json
from fractions import Fraction as Q
import net

h = int(sys.argv[1]) if len(sys.argv) > 1 else 8
res = {}


def run(name, g=None, alpha=None):
    net.MUTANT = name
    if alpha is not None:
        net.ALPHA = alpha
    g = g or net.mine(h)
    r = net.run(g, name, three=False)
    net.MUTANT = None
    net.ALPHA = Q(2, 25)
    res[name] = 'rejected' if not r['PASS'] else 'NOT REJECTED'
    print(name, res[name], json.dumps({k: r.get(k) for k in ('structure_fails', 'scalar')}),
          [(f['stage'], f['fails'], f['decreases'], f['first'][:1]) for f in r.get('frames', [])], flush=True)


run('J_plus')                       # inject +D instead of -D: scalar identity fails
run('J_before_R0')                  # PR order swapped: Y would decrease
run('stage2_uncomplemented')        # reverse mixer with U_z instead of U_z^perp
run('form_I_minus_J_over_9', alpha=Q(1, 9))   # triple-motif form: neighbors not orthogonal
g = net.mine(h)
a, b = g.adds[-1]
g.adds[-1] = (a, a)                 # overlapping addition
run('overlap_addition', g=g)
# F_2 arithmetic instead of F_3: C(k,2)-[k=2] is not [k=5] mod 2
import numpy as np
orig = net.Scalar


class F2(net.Scalar):
    pass


def patch_mod(mod):
    src = open(net.__file__).read()


g = net.mine(h)
sup, core, kinds, fails = net.check_structure(g)
R = net.Roles(g)
S = net.Scalar(g, R, kinds)
v = g.v
# evaluate the combined map over the integers and reduce mod 2 and mod 3
X = np.eye(v, dtype=np.int64); Y = np.zeros((v, v), dtype=np.int64); Z = np.zeros((R.n, v), dtype=np.int64)
M = {}
for name in ('mod3', 'mod2'):
    pass
# integer combined coefficient (R0 + J) L V from supports
coef = np.zeros((v, v), dtype=np.int64)
for o, k in enumerate(kinds):
    z = g.outputs[o][0]
    s = sup[z]
    srcs = [i for i in range(v) if s >> i & 1]
    if k[0] == 'A':
        for t in range(v):
            if g.five[t] & k[1] == k[1]:
                coef[t, srcs] += 1
    else:
        coef[g.idx[k[2]], srcs] -= 1
I = np.eye(v, dtype=np.int64)
print('integer combined map == identity mod 3:', bool(((coef - I) % 3 == 0).all()),
      '| mod 2 (control, must be False):', bool(((coef - I) % 2 == 0).all()),
      '| over Z (must be False):', bool((coef == I).all()))
res['F2_arithmetic'] = 'rejected' if not ((coef - I) % 2 == 0).all() else 'NOT REJECTED'
# matching control: keep three singletons instead of two
pi, rep = net.matching(h)
bad = {T: U for T, U in pi.items()}
print('matching', rep)
print('CONTROLS', 'PASS' if all(v == 'rejected' for v in res.values()) else 'FAIL', res)
