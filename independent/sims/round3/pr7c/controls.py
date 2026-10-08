"""Negative controls for the PR 7 complex adapter (each must be rejected)."""
import sys, os
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'lib', 'complexsrc'))
import adapter, flevel, recipes, pr3
from circuit import Roles
h = int(sys.argv[1]) if len(sys.argv) > 1 else 10
res = {}


def frames_ok(C, recipe):
    out = flevel.run(C, Roles(C), recipe, pr3.label_space, verbose=False)
    return all(not o['fails'] and o['n_dec'] == h + 1 for o in out.values())


base = adapter.their_dag(h)
C, sup, _ = adapter.convert(base, h)
assert adapter.coefficient_check(C, sup)['ok'] and frames_ok(C, recipes.pr3_invocation)
# 1 flip the coefficient of one piece
C, sup, _ = adapter.convert(base, h)
z, t, c = C.outputs[0]; C.outputs[0] = (z, t, -c)
res['flip_coefficient'] = not adapter.coefficient_check(C, sup)['ok']
# 2 drop one piece
C, sup, _ = adapter.convert(base, h)
C.outputs.pop(); res['drop_piece'] = not adapter.coefficient_check(C, sup)['ok']
# 3 undo the injection rule for one target: inject its full disjoint sum
#   (an existing DAG node) as a single +1/2 piece instead of the split pieces
C, sup, _ = adapter.convert(base, h)
t = 0
ks = [k for k, (z, tt, c) in enumerate(C.outputs) if tt == t and c > 0]
z0 = C.outputs[ks[0]][0]
for k in ks[1:]:
    z1 = C.outputs[k][0]
    s01 = sup[z0] | sup[z1]
    cov = 0
    x = s01
    while x:
        lb = x & -x; cov |= C.T[lb.bit_length() - 1]; x ^= lb
    z0n = C.add(z0, z1, 'd0', ('coord', cov)); sup[z0n] = s01; z0 = z0n
C.outputs = [o for k, o in enumerate(C.outputs) if k not in ks] + [(z0, t, Fraction(1, 2))]
done = len(ks) > 1
r = adapter.coefficient_check(C, sup)
res['unsplit_full_cover_piece'] = done and r['full_cover_pieces'] > 0 and not frames_ok(C, recipes.pr3_invocation)
# 4 reverse orientation with forward (uncomplemented) node labels
C, sup, _ = adapter.convert(base, h)


def bad(C, R, reverse=False):
    inv = recipes.pr3_invocation(C, R, reverse)
    inv.gates = [(tg, w, (fr[0], fr[1][1]) if isinstance(fr[1], tuple) and fr[1][0] == 'perp' else fr) for tg, w, fr in inv.gates]
    return inv
res['reverse_uncomplemented'] = not frames_ok(C, bad)
print(res)
print('CONTROLS', 'PASS' if all(res.values()) else 'FAIL')
