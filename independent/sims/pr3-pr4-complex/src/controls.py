"""Negative controls: the checkers must reject known-bad variants."""
from fractions import Fraction
import pr3, pr4, recipes, flevel, coeff
from circuit import Roles
from network import F_KEY, Z_KEY, node_key, Invocation
from f2 import Space, nondegenerate, perp


def pr3_without_injection_rule(h=9):
    B = pr3.PR3Builder(h)
    B.inject_orig = B.inject

    def inject(z, S, c, log):
        if z is not None:
            B.C.outputs.append((z, B.C.tidx[S], c))
    B.inject = inject
    C = B.build()
    R = Roles(C)
    out = flevel.run(C, R, recipes.pr3_invocation, pr3.label_space, stages=(1,), verbose=False)
    f = out[1]['fails']
    return dict(n_fail=len(f), example=f[0] if f else None)


def pr3_reverse_with_forward_labels(h=8):
    C = pr3.build(h)
    R = Roles(C)

    def bad(C, R, reverse=False):
        inv = recipes.pr3_invocation(C, R, reverse)
        if reverse:
            inv.gates = [(t, w, (F_KEY, fr[1][1]) if t == 'Linv_mid' else fr) for t, w, fr in inv.gates]
        return inv
    out = flevel.run(C, R, bad, pr3.label_space, stages=(2,), verbose=False)
    f = out[2]['fails']
    return dict(n_fail=len(f), example=f[0] if f else None)


def pr3_flip_coefficient(h=8):
    C = pr3.build(h)
    z, t, c = C.outputs[0]
    C.outputs[0] = (z, t, -c)
    ok, _, f = coeff.check_side_map(C)
    return dict(map_ok=ok, example=f[0] if f else None)


def pr4_without_repair(h=8):
    plan = pr4.plan_disjoint(h)
    C0 = pr4.build(h, plan)
    # rebuild with repair disabled
    import pr4 as P
    full = (1 << h) - 1
    orig_any = any

    C = Circuit_no_repair(h, plan)
    R = Roles(C)
    out = flevel.run(C, R, recipes.pr4_invocation, pr4.label_space, stages=(1,), verbose=False)
    f = out[1]['fails']
    return dict(repaired_in_real_build=C0.repaired, n_fail=len(f), example=f[0] if f else None)


def Circuit_no_repair(h, plan):
    """pr4.build with the rectangle repair rule switched off."""
    src = pr4.build.__code__
    import types
    g = dict(pr4.__dict__)
    g['any'] = lambda it: False
    f = types.FunctionType(src, g)
    return f(h, plan)


def pr4_injection_before_scatter(h=8):
    """Swap middle R and J frames' order: J (t^perp) then R (D_0) on targets
    creates a decreasing target edge; the note says the order is essential."""
    C = pr4.build(h)
    R = Roles(C)

    def bad(C, R, reverse=False):
        inv = recipes.pr4_invocation(C, R, reverse)
        if not reverse:
            gs = inv.gates
            iR = [i for i, g in enumerate(gs) if g[0] == 'R']
            iJ = [i for i, g in enumerate(gs) if g[0] == 'J']
            Rg = [gs[i] for i in iR]
            Jg = [gs[i] for i in iJ]
            rest = [g for g in gs if g[0] not in ('R', 'J')]
            k = [i for i, g in enumerate(rest) if g[0] == 'Llate_inv'][0]
            inv.gates = rest[:k] + Jg + Rg + rest[k:]
        return inv
    out = flevel.run(C, R, bad, pr4.label_space, stages=(1, 3), verbose=False)
    return dict(n_fail_stage3=len(out[3]['fails']), n_dec_stage3=out[3]['n_dec'], loss_stage3=out[3]['loss'],
                example=out[3]['fails'][0] if out[3]['fails'] else None)


def pr4_odd_h_labels(h=9):
    """w_i = c + e_i orthonormal needs even h: at odd h, S_i is degenerate."""
    from f2 import dot
    c = (1 << h) - 1
    w = [c ^ (1 << k) for k in range(h)]
    gram_identity = all(dot(w[i], w[j]) == (i == j) for i in range(h) for j in range(h))
    star = Space(h, [3 | (1 << k) for k in range(2, h)])   # pair {0,1} root label
    wspan = Space(h, [w[k] for k in range(2, h)])
    return dict(h=h, w_gram_is_identity=gram_identity, pair_root_equals_span_w=(star == wspan))


def pr4_flip_scatter(h=8):
    C = pr4.build(h)
    orig = pr4.scatter_rows

    def bad(C):
        rows = orig(C)
        r0 = rows[0]
        k = next(iter(r0))
        r0[k] = -r0[k]
        return rows
    pr4.scatter_rows = bad
    try:
        ok, _, f = pr4.check_map(C)
    finally:
        pr4.scatter_rows = orig
    return dict(map_ok=ok, example=f[0] if f else None)


def run_all():
    res = {}
    for name, fn in [('pr3_without_injection_rule', pr3_without_injection_rule),
                     ('pr3_reverse_with_forward_labels', pr3_reverse_with_forward_labels),
                     ('pr3_flip_coefficient', pr3_flip_coefficient),
                     ('pr4_without_repair', pr4_without_repair),
                     ('pr4_injection_before_scatter', pr4_injection_before_scatter),
                     ('pr4_odd_h_labels', pr4_odd_h_labels),
                     ('pr4_flip_scatter', pr4_flip_scatter)]:
        res[name] = fn()
        print(' ', name, res[name])
    return res
