"""Compare the own rebuild with PR 8's explore.Circuit (second signal):
same set of addition supports, same decompositions, same outputs."""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'lib', 'complexsrc'))
import build
n = int(sys.argv[1])
C = build.build(n)
sys.path.insert(0, os.path.join(HERE, '..', 'pr8', 'research', 'geometric-complex'))
from explore import Circuit
for fam, rel in (('D', 'disjoint'), ('E', 'intersection_two')):
    c = Circuit(n, rel)
    theirs = {c.support[z] for z in c.active if c.args[z] is not None}
    tdec = {(c.support[z], frozenset((c.support[a], c.support[b]))) for z in c.active if c.args[z] is not None for a, b in [c.args[z]]}
    mine = {C.sup[z] for z in range(C.v, C.n_nodes()) if C.family[z] == fam}
    mdec = {(C.sup[z], frozenset((C.sup[C.args[z][0]], C.sup[C.args[z][1]]))) for z in range(C.v, C.n_nodes()) if C.family[z] == fam}
    print(n, fam, 'theirs', len(theirs), 'mine', len(mine), 'same supports', theirs == mine, 'same decompositions', tdec == mdec)
