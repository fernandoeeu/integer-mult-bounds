"""Exact phase identity (Gaussian phases as exponents mod 4) for every distinct
F-level residual pair met by the PR 4 head invocation, all x in F_2^h."""
import sys, time
import pr4new, phase
from circuit import Roles
from network import Labels, EdgeChecker, check_invocation, data_terminals
from f2 import Space
for h in [int(a) for a in sys.argv[1:]]:
    t = time.time()
    C = pr4new.build(h); R = Roles(C)
    labels = Labels(C, lambda key: pr4new.label_space(C, key, Space))
    ec = EdgeChecker(labels)
    for j in (1, 2, 3):
        inv = pr4new.invocation(C, R, reverse=(j == 2)); s, k = data_terminals(inv)
        check_invocation(inv, labels, j, s, k, ec=ec)
    n, ok = phase.run_from_checker(ec, labels, h)
    print('h', h, 'distinct residual pairs', n, 'phase identity holds on', ok, 'PASS' if n == ok else 'FAIL',
          '%.1fs' % (time.time() - t))
