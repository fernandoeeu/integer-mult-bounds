import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src'))
import pr4, flevel, recipes
from circuit import Roles
print('PR4 with an independent half-split rectangle plan (not the PR selection):')
for h in (8,10,12):
    C=pr4.build(h, pr4.plan_disjoint(h,'half')); R=Roles(C)
    ok,_,_=pr4.check_map(C)
    out=flevel.run(C,R,recipes.pr4_invocation,pr4.label_space,verbose=False)
    print(' h',h,'roles',R.n_roles,'repaired',C.repaired,'map ok',ok,'frame failures',[len(out[j]['fails']) for j in (1,2,3)],'loss',[out[j]['loss'] for j in (1,2,3)])
