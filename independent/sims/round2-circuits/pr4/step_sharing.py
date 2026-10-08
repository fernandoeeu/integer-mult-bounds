"""Stage-1/3 bank sharing for the PR 4 head: partner-flip pi combinatorics,
the join E subset H as actual subspaces of F^{(x)3} (h=6, all pairs), and the
endpoint frames (every auxiliary ends stage 1 at D_1, starts stage 3 at D_0)."""
import sys, time
import sharing, pr4new
from circuit import Roles
for h in (6, 8, 10, 24):
    print('pi combinatorics h', h, sharing.combinatorics(h))
t = time.time()
from circuit import triples
T, _ = triples(6)
pairs = [(A, B) for A in range(len(T)) for B in range(len(T)) if A % 7 == 0 or B % 7 == 0][:28]
r = sharing.join_check(6, pairs)
print('join h6 pairs', len(r), 'ok', all(x[2] and x[3] for x in r), '%.1fs' % (time.time() - t))
for h in [int(a) for a in sys.argv[1:]]:
    C = pr4new.build(h); R = Roles(C)
    bad = sharing.endpoint_frames(pr4new.invocation(C, R), pr4new.invocation(C, R))
    print('endpoint frames h', h, 'aux roles', R.n_roles, 'bad', len(bad))
