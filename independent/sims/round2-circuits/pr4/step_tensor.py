"""Tensor-level check (actual subspaces of F^{(x)3}, F = F_2^h) of one
invocation per stage for the PR 4 head construction, small h."""
import sys, time
from circuit import Roles
from network import Labels
from f2 import Space
import pr4new, tensor
h = int(sys.argv[1]); sample = float(sys.argv[2]) if len(sys.argv) > 2 else 1.0
C = pr4new.build(h); R = Roles(C)
labels = Labels(C, lambda key: pr4new.label_space(C, key, Space))
T = C.T
for a in [(T[0], T[len(T) // 3], T[-1])]:
    print('h', h, 'roles', R.n_roles, 'a', [bin(x) for x in a])
    print(' interstage', tensor.data_terminal_consistency(labels, h, a))
    for j in (1, 2, 3):
        t = time.time()
        inv = pr4new.invocation(C, R, reverse=(j == 2))
        rep = tensor.check_stage(inv, labels, j, a, sample)
        loss = sum(d for _, d in rep['dec'])
        print(f'  stage {j}: fails {len(rep["fails"])} residuals {rep["n_res"]} onb-built {rep["n_onb"]} '
              f'dec {len(rep["dec"])} loss {loss} sum|d| {rep["tot_abs"]} ({time.time()-t:.1f}s)')
        for f in rep['fails'][:3]:
            print('   FAIL', f)
        sys.stdout.flush()
