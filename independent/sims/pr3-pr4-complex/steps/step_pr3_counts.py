import sys, time
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src'))
import pr3, coeff
from circuit import Roles
for h in [int(a) for a in sys.argv[1:] if a.isdigit()]:
    t=time.time()
    C=pr3.build(h)
    fam={}
    for k,f in zip(C.kind,C.family):
        if k=='add': fam[f]=fam.get(f,0)+1
    R=Roles(C)
    ppt=set(C.pieces_per_target.values())
    print(h, 'adds',fam, 'outputs',len(C.outputs),'roles',R.n_roles,'c+q',C.n_add()+len(C.outputs),'splits',len(C.split_log),'pieces/target',ppt, '%.1fs'%(time.time()-t))
    if h<=14 or "--coeff" in sys.argv:
        ok,nnz,f=coeff.check_side_map(C); print('  coeff ok',ok,'nnz',nnz,f[:3])
