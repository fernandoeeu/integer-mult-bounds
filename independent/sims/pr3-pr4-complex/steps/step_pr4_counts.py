import sys, time
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src'))
import pr4
from circuit import Roles
for h in [int(a) for a in sys.argv[1:] if a.isdigit()]:
    t=time.time()
    C=pr4.build(h); R=Roles(C)
    print(h,'rect adds',C.rect_adds,'rect outs',C.q0,'repaired',C.repaired,'global',C.global_adds,'pair',C.pair_adds,'pair q',C.pair_q,'point',C.point_adds,
          'C',C.n_add(),'q',len(C.outputs),'roles',R.n_roles,'%.1fs'%(time.time()-t))
    if h<=12 or '--coeff' in sys.argv:
        print('  map',pr4.check_map(C)[:2])
