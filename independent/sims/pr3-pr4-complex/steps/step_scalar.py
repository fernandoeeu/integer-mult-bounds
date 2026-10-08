import sys, time
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src'))
import pr3, pr4, scalar
from circuit import Roles
which=sys.argv[1]
for h in [int(a) for a in sys.argv[2:] if a.isdigit()]:
    t=time.time()
    mod = pr3 if which=='pr3' else pr4
    C=mod.build(h); R=Roles(C); M=scalar.Motif(C,R,which)
    print(which,h,'single',scalar.single_invocation(M), '%.1fs'%(time.time()-t))
    if '--three' in sys.argv:
        print('   three-stage', scalar.three_stage(M, shared=(which=='pr4')), '%.1fs'%(time.time()-t))
