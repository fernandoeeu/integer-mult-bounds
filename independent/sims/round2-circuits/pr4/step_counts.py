"""Counts, totals, exact coefficient map for PR 4 head (8c225e6) construction."""
import sys, time
from circuit import Roles
import pr3, pr4new
for h in [int(a) for a in sys.argv[1:] if a.isdigit()]:
    t = time.time()
    base = pr3.build(h)
    C = pr4new.build(h)
    R = Roles(C)
    q = len(C.outputs)
    side_q = sum(1 for _, t_, _ in C.outputs if not isinstance(t_, tuple))
    out = dict(h=h, base_additions=base.n_add(), base_outputs=len(base.outputs),
               additions=C.n_add(), new_ancestors=C.n_add() - base.n_add(),
               side_outputs=side_q, q=q, roles=R.n_roles, roles_eq_C_plus_q=R.n_roles == C.n_add() + q)
    out['totals_exact'] = not pr4new.check_totals(C)
    if h <= 14 or '--map' in sys.argv:
        ok, fails, maxc = pr4new.check_map(C)
        out['map_exact'] = ok; out['map_fails'] = fails[:3]; out['max_pass_coeff'] = str(maxc)
    out['secs'] = round(time.time() - t, 1)
    print(out); sys.stdout.flush()
