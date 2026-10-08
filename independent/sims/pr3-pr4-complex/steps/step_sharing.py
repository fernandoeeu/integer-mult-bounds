import sys, random, time
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src'))
import sharing, pr4, recipes
from circuit import Roles
for h in (6,8,10,24): print('pi combinatorics h',h,sharing.combinatorics(h))
t=time.time()
v=20; r=sharing.join_check(6,[(A,B) for A in range(v) for B in range(v)]) if "--full6" in sys.argv else sharing.join_check(6,[(A,B) for A in range(0,20,3) for B in range(0,20,5)])
print('h6 pairs (all 400 with --full6)', len(r), 'ok', all(x[2] and x[3] for x in r), '%.1fs'%(time.time()-t))
rng=random.Random(3); v=56
pairs=[(rng.randrange(v),rng.randrange(v)) for _ in range(4)]+[(0,0),(5,5)]
r=sharing.join_check(8,pairs)
print('h8 sampled pairs', len(r), 'ok', all(x[2] and x[3] for x in r), '%.1fs'%(time.time()-t))
for h in (8,10,24):
    C=pr4.build(h); R=Roles(C)
    bad=sharing.endpoint_frames(recipes.pr4_invocation(C,R,False),recipes.pr4_invocation(C,R,False))
    print('endpoint frames h',h,'aux roles',R.n_roles,'bad',len(bad))
