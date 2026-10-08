"""F_2-level frame/residual check (both factors of D(B',P')) of one invocation
per stage for the PR 4 head construction. Prints failures, decreasing edges,
and the loss per stage (doc: ell = (h-1)^2 + h)."""
import sys, time
from circuit import Roles
import pr4new, flevel
variant = next((a.split('=')[1] for a in sys.argv if a.startswith('--variant=')), None)
for h in [int(a) for a in sys.argv[1:] if a.isdigit()]:
    t = time.time()
    C = pr4new.build(h)
    R = Roles(C)
    rec = lambda C_, R_, reverse=False: pr4new.invocation(C_, R_, reverse, variant)
    print('h', h, 'roles', R.n_roles, 'variant', variant)
    out = flevel.run(C, R, rec, pr4new.label_space)
    allok = True
    for j, r in out.items():
        kinds = {}
        for (a, b, l), n in r['dec_kinds'].items():
            kinds[(str(a), str(b), l)] = n
        ok = not r['fails'] and r['loss'] == (h - 1) ** 2 + h and r['n_dec'] == h
        allok &= ok
        print('  stage', j, 'ok', ok, 'loss', r['loss'], 'expected', (h - 1) ** 2 + h, 'n_dec', r['n_dec'],
              'dec kinds', len(kinds), 'sample', list(kinds.items())[:2])
    print('  RESULT', 'PASS' if allok else 'FAIL', '%.1fs' % (time.time() - t))
    sys.stdout.flush()
