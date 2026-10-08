"""Exact dyadic scalar runs for the PR 4 head construction: single invocation
(forward y+=x, inverse y-=x, dirty scratch restored, every basis vector at
small h) and the three-stage exchange with partner-flip stage-1/3 bank sharing."""
import sys, time
from circuit import Roles
import pr4new, scalar
three = '--three' in sys.argv
for h in [int(a) for a in sys.argv[1:] if a.isdigit()]:
    t = time.time()
    C = pr4new.build(h)
    R = Roles(C)
    M = pr4new.Motif(C, R)
    s = scalar.single_invocation(M)
    print('h', h, 'single', s, 'max pass coeff', M.max_coeff, '%.1fs' % (time.time() - t)); sys.stdout.flush()
    if three:
        t = time.time()
        r = scalar.three_stage(M, shared=True)
        print('   three-stage shared', r, '%.1fs' % (time.time() - t)); sys.stdout.flush()
