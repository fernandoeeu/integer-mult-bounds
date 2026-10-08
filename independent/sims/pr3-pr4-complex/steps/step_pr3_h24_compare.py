import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src'))
import pr3, params
from circuit import Roles
C=pr3.build(24); R=Roles(C); c=params.pr3_counts(24,R.n_roles)
print('PR3 construction at h=24 (PR4 ground size): roles',R.n_roles,'additions',C.n_add(),'outputs',len(C.outputs),'eta',c['eta'],'~',float(c['eta']))
