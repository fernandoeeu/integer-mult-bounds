"""Tensor-level (actual subspaces of F_2^{h^3}) and phase-identity checks for
PR 8 (own rebuild) and PR 7's complex circuit, reusing lib/complexsrc.
Usage: python3 step_tensor_phase.py pr8 n sample | pr7c h sample"""
import sys, os, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'complexsrc'))
import tensor, phase, pr3, recipes
from circuit import Roles
from network import Labels, EdgeChecker, check_invocation, data_terminals
from f2 import Space
which, size = sys.argv[1], int(sys.argv[2])
sample = float(sys.argv[3]) if len(sys.argv) > 3 else 1.0
if which == 'pr8':
    sys.path.insert(0, os.path.join(HERE, '..', 'pr8geo'))
    import build
    C = build.build(size); rec = build.geo_invocation
else:
    sys.path.insert(0, os.path.join(HERE, '..', 'pr7c'))
    import adapter
    C, sup, fails = adapter.convert(adapter.their_dag(size), size); assert not fails
    rec = recipes.pr3_invocation
R = Roles(C); h = C.h
labels = Labels(C, lambda key: pr3.label_space(C, key, Space))
T = C.T
a = (T[0], T[len(T) // 3], T[-1])
print(which, size, 'label dim', h, 'roles', R.n_roles)
print(' interstage', tensor.data_terminal_consistency(labels, h, a))
ok = True
for j in (1, 2, 3):
    t = time.time()
    inv = rec(C, R, reverse=(j == 2))
    rep = tensor.check_stage(inv, labels, j, a, sample)
    ok &= not rep['fails']
    print(f' stage {j}: fails {len(rep["fails"])} residuals {rep["n_res"]} onb-built {rep["n_onb"]} dec {len(rep["dec"])} '
          f'loss {sum(d for _, d in rep["dec"])} sum|d| {rep["tot_abs"]} ({time.time()-t:.1f}s)', flush=True)
    for f in rep['fails'][:3]: print('   FAIL', f)
ec = EdgeChecker(labels)
for j in (1, 2, 3):
    inv = rec(C, R, reverse=(j == 2)); s, k = data_terminals(inv)
    check_invocation(inv, labels, j, s, k, ec=ec)
n, okp = phase.run_from_checker(ec, labels, h)
print(' phase identity on', n, 'distinct F-level residual pairs, all x:', okp)
print('TENSOR+PHASE', 'PASS' if ok and okp else 'FAIL')
