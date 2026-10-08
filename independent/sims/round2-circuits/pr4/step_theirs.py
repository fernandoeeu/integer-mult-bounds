"""Our verifier applied to the PR's own node list (non-independent signal)."""
import sys, time
from circuit import Roles
import pr4new, flevel, scalar, fromtheirs
checkout = sys.argv[1]
for h in [int(a) for a in sys.argv[2:] if a.isdigit()]:
    t = time.time()
    C = fromtheirs.load(checkout, h)
    R = Roles(C)
    ok_map, fails, maxc = pr4new.check_map(C) if (h <= 14 or '--map' in sys.argv) else (None, [], None)
    print('PR graph h', h, 'additions', C.n_add(), 'outputs', len(C.outputs), 'roles', R.n_roles,
          'totals exact', not pr4new.check_totals(C), 'map', ok_map, '%.1fs' % (time.time() - t))
    if '--frames' in sys.argv:
        out = flevel.run(C, R, pr4new.invocation, pr4new.label_space)
        print('  frames', {j: (len(r['fails']), r['loss'], r['n_dec']) for j, r in out.items()})
    if '--scalar' in sys.argv:
        print('  scalar', scalar.single_invocation(pr4new.Motif(C, R)))
    sys.stdout.flush()
