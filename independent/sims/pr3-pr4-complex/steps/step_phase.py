import sys, time
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src'))
import pr3, pr4, recipes, phase
from circuit import Roles
from network import Labels, EdgeChecker, check_invocation, data_terminals
from f2 import Space
for which,h in (('pr3',8),('pr4',8)):
    t=time.time()
    mod = pr3 if which=='pr3' else pr4
    rec = recipes.pr3_invocation if which=='pr3' else recipes.pr4_invocation
    C=mod.build(h); R=Roles(C)
    labels=Labels(C, lambda key: mod.label_space(C,key,Space))
    ec=EdgeChecker(labels)
    for j in (1,2,3):
        inv=rec(C,R,reverse=(j==2)); s,k=data_terminals(inv)
        check_invocation(inv,labels,j,s,k,ec=ec)
    n,ok=phase.run_from_checker(ec,labels,h)
    print(which,'h',h,'distinct residual pairs',n,'phase identity holds for all x on',ok,'%.1fs'%(time.time()-t))
