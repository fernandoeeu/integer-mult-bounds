import sys, time
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src'))
import pr3, pr4, recipes, tensor
from circuit import Roles
from network import Labels, Invocation
from f2 import Space
which=sys.argv[1]; h=int(sys.argv[2]); sample=float(sys.argv[3]) if len(sys.argv)>3 else 1.0
mod = pr3 if which=='pr3' else pr4
rec = recipes.pr3_invocation if which=='pr3' else recipes.pr4_invocation
C=mod.build(h); R=Roles(C)
labels=Labels(C, lambda key: mod.label_space(C,key,Space))
T=C.T
a=(T[0], T[len(T)//3], T[-1])
print(which,'h',h,'roles',R.n_roles,'a',[bin(x) for x in a])
print(' interstage', tensor.data_terminal_consistency(labels,h,a))
tot={}
for j in (1,2,3):
    t=time.time()
    inv=rec(C,R,reverse=(j==2))
    rep=tensor.check_stage(inv,labels,j,a,sample)
    tot[j]=rep['tot_abs']
    print(f' stage {j}: fails {len(rep["fails"])} residuals {rep["n_res"]} onb-built {rep["n_onb"]} dec {len(rep["dec"])} loss {sum(d for _,d in rep["dec"])} sum|d| {rep["tot_abs"]} ({time.time()-t:.1f}s)')
    for f in rep['fails'][:3]: print('   FAIL',f)
print(' totals',tot)
