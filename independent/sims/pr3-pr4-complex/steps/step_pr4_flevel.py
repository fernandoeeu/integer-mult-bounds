import sys
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src'))
import pr4, flevel, recipes
from circuit import Roles
for h in [int(a) for a in sys.argv[1:]]:
    C=pr4.build(h); R=Roles(C)
    print('h',h,'roles',R.n_roles)
    out=flevel.run(C,R,recipes.pr4_invocation,pr4.label_space)
    for j,o in out.items():
        print('  ',j,{(str(a[1]) [:40],str(b[1])[:40],l):n for (a,b,l),n in o['dec_kinds'].items()})
