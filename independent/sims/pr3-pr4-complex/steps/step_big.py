import sys, time
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src'))
import pr3, pr4, scalar
from circuit import Roles
t=time.time()
C=pr4.build(24)
print('pr4 h24 exact map', pr4.check_map(C)[:2], '%.0fs'%(time.time()-t)); sys.stdout.flush()
R=Roles(C); M=scalar.Motif(C,R,'pr4')
print('pr4 h24 single invocation', scalar.single_invocation(M, cols=3), '%.0fs'%(time.time()-t)); sys.stdout.flush()
C=pr3.build(25); R=Roles(C); M=scalar.Motif(C,R,'pr3')
print('pr3 h25 single invocation', scalar.single_invocation(M, cols=3), '%.0fs'%(time.time()-t))
