"""Negative controls for the PR 8 rebuild (each must be rejected), n = 7."""
import sys, os
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'lib', 'complexsrc'))
import build, flevel, pr3, scalar
from circuit import Roles
n = int(sys.argv[1]) if len(sys.argv) > 1 else 7
res = {}


def frames_ok(C, recipe=build.geo_invocation):
    out = flevel.run(C, Roles(C), recipe, pr3.label_space, verbose=False)
    return all(not o['fails'] and o['n_dec'] == n + 1 for o in out.values())


C = build.build(n)
assert frames_ok(C) and build.coefficient_check(C)['ok']
# 1 the note's own control: no extra label coordinate
res['no_extra_coordinate'] = not frames_ok(build.build(n, star=False))
# 2 E nodes labelled by coordinate envelopes (as the D nodes)
C = build.build(n)
for z in range(C.v, C.n_nodes()):
    if C.family[z] == 'E':
        C.label[z] = ('coord', C.label[z][1] | C.label[z][2])
res['E_coordinate_labels'] = not frames_ok(C)
# 3 inject E with +1/2: scalar identity fails
C = build.build(n)
C.outputs = [(z, t, -c if c < 0 else c) for z, t, c in C.outputs]
M = scalar.Motif(build.ScalarView(C), Roles(C), 'pr3')
r = scalar.single_invocation(M)
res['E_plus_half'] = not r['forward']['target']
# 4 reverse orientation with uncomplemented mixer labels


def bad(C, R, reverse=False):
    inv = build.geo_invocation(C, R, reverse)
    inv.gates = [(tg, w, (fr[0], fr[1][1]) if isinstance(fr[1], tuple) and fr[1][0] == 'perp' else fr) for tg, w, fr in inv.gates]
    return inv
res['reverse_uncomplemented'] = not frames_ok(build.build(n), bad)
# 5 one D output with a target point added to its envelope label
C = build.build(n)
z, t, c = next(o for o in C.outputs if o[2] > 0 and C.kind[o[0]] == 'add')
C.label[z] = ('coord', C.label[z][1] | (C.T[t] & -C.T[t]))
res['D_label_meets_target'] = not frames_ok(C)
print(res)
print('CONTROLS', 'PASS' if all(res.values()) else 'FAIL')
