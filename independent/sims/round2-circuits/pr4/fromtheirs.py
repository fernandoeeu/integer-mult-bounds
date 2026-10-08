"""Load the PR's own RetainedComplexCircuit graph into our Circuit container,
so that our verifier (map, totals, F_2 frames, scalar runs) can be applied to
the PR's exact node list. Second, non-independent signal."""
import sys
import os
from fractions import Fraction
from circuit import Circuit


def load(checkout, h):
    sys.path.insert(1, os.path.join(checkout, 'scripts'))
    from retained_complex import RetainedComplexCircuit
    t = RetainedComplexCircuit(h)
    C = Circuit(h)
    v = C.v
    assert [sum(1 << p for p in x) for x in t.inputs] == C.T
    ren = {n: n - 1 for n in range(1, v + 1)}
    for n in sorted(x for x in t.active if t.args[x]):
        a, b = t.args[n]
        lab = t.labels[n]
        key = ('coord', lab[1]) if lab[0] == 'coordinate' else ('star', lab[1], lab[2])
        ren[n] = C.add(ren[a], ren[b], 'pr', key)
    for idx, node in sorted(t.outputs.items()):
        if idx < len(t.targets):
            tgt, sign = t.targets[idx]
            C.outputs.append((ren[node], C.tidx[tgt], Fraction(sign, 2)))
        else:
            k = idx - len(t.targets)
            C.outputs.append((ren[node], ('tot', '*' if k == h - 1 else k), Fraction(1)))
    return C
