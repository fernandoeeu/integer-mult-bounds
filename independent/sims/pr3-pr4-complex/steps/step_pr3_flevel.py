import sys
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src'))
import pr3, flevel, recipes
from circuit import Roles
for h in [int(a) for a in sys.argv[1:]]:
    C=pr3.build(h); R=Roles(C)
    print('h',h,'roles',R.n_roles)
    out=flevel.run(C,R,recipes.pr3_invocation,pr3.label_space)
    for j,o in out.items(): print('  ',j,o['dec_kinds'])
