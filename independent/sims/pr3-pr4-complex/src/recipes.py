"""Schedules and frame assignments, transcribed from each PR's note.

PR 3 (notes/complex-circuit-construction.tex, 'The transparent schedule',
'Frames in both stage directions'):
  forward  L, -J, L^-1, -R, V, G, R, L, J, L^-1, G^-1, V^-1
  early mixers and early injection D_0; middle node gates D_{U_z};
  copy gates physical X frame D_<t_T>; injection physical Y frame D_{t_S^perp};
  late cleanup D_1.  Central gates as in the original table.
  inverse: V, G, L, -J, L^-1, -R, G^-1, V^-1, R, L, J, L^-1 with
  'D_{U_z^perp} to node z [in the first L^-1], D_0 to the preceding L, and
  D_1 to the second L, J and L^-1'; physical frames as in the original.

PR 4 (notes/retained-complex-construction.tex):
  forward  L, -R, -J, L^-1, V, L, R, J, L^-1, -V
  'Early mixer and scatter gates use D_0; late cleanup uses D_1. The forward
  source copy uses source-line frames, the middle mixer uses D_U, the entire
  retained-total scatter uses the common frame D_0, and only then the side
  injection uses each target-complement frame.'  The early -J is not named;
  it is read as an early gate at D_0 (any other choice would create extra
  decreasing edges on output roles).
  reverse: 'The reverse scatter uses D_1, followed by the complemented
  inverse mixer at D_{U^perp}'.
"""
from network import Invocation, F_KEY, Z_KEY, node_key

D0 = (F_KEY, Z_KEY)
D1 = (F_KEY, F_KEY)


def pr3_invocation(C, R, reverse=False):
    h = C.h
    inv = Invocation(C, R, n_center=h + 1)
    v = C.v
    allX = [inv.X(T) for T in range(v)]
    allY = [inv.Y(T) for T in range(v)]
    cen = list(range(2 * v, 2 * v + h + 1))
    nk = lambda z: node_key(C, z)
    if not reverse:
        inv.mixers('L0', lambda z: D0)
        inv.injections('-J0', 'Y', lambda S: D0)
        inv.mixers('L0inv', lambda z: D0, inverse=True)
        inv.gate('-R', allY + cen, D0)
        inv.copies('V', 'X', lambda T: (F_KEY, ('line', T)))
        inv.gate('G', allX + cen, D1)
        inv.gate('R', allY + cen, D0)
        inv.mixers('Lmid', lambda z: (F_KEY, nk(z)))
        inv.injections('J', 'Y', lambda S: (F_KEY, ('tperp', S)))
        inv.mixers('Llate_inv', lambda z: D1, inverse=True)
        inv.gate('Ginv', allX + cen, D1)
        inv.copies('Vinv', 'X', lambda T: D1)
    else:
        inv.copies('V', 'Y', lambda T: (('line', T), Z_KEY))
        inv.gate('G', allY + cen, D0)
        inv.mixers('L', lambda z: D0)
        inv.injections('-J', 'X', lambda S: (F_KEY, ('line', S)))
        inv.mixers('Linv_mid', lambda z: (F_KEY, ('perp', nk(z))), inverse=True)
        inv.gate('-R', allX + cen, D1)
        inv.gate('Ginv', allY + cen, D0)
        inv.copies('Vinv', 'Y', lambda T: (F_KEY, ('tperp', T)))
        inv.gate('R', allX + cen, D1)
        inv.mixers('L2', lambda z: D1)
        inv.injections('J2', 'X', lambda S: D1)
        inv.mixers('L2inv', lambda z: D1, inverse=True)
    return inv


def pr4_invocation(C, R, reverse=False):
    """PR 4: no central wires; retained totals are DAG outputs with target
    tag ('tot', i) and are scattered by one R gate touching all targets."""
    inv = Invocation(C, R, n_center=0)
    v = C.v
    allX = [inv.X(T) for T in range(v)]
    allY = [inv.Y(T) for T in range(v)]
    tot_roles = [inv.role(R.out_role[k]) for k, (z, t, c) in enumerate(C.outputs)
                 if isinstance(t, tuple)]
    side = lambda t: not isinstance(t, tuple)
    nk = lambda z: node_key(C, z)
    if not reverse:
        inv.mixers('L0', lambda z: D0)
        inv.gate('-R0', allY + tot_roles, D0)
        inv.injections('-J0', 'Y', lambda S: D0, side)
        inv.mixers('L0inv', lambda z: D0, inverse=True)
        inv.copies('V', 'X', lambda T: (F_KEY, ('line', T)))
        inv.mixers('Lmid', lambda z: (F_KEY, nk(z)))
        inv.gate('R', allY + tot_roles, D0)
        inv.injections('J', 'Y', lambda S: (F_KEY, ('tperp', S)), side)
        inv.mixers('Llate_inv', lambda z: D1, inverse=True)
        inv.copies('-V', 'X', lambda T: D1)
    else:
        inv.copies('V', 'Y', lambda T: (('line', T), Z_KEY))
        inv.mixers('L', lambda z: D0)
        inv.injections('-J', 'X', lambda S: (F_KEY, ('line', S)), side)
        inv.gate('-R', allX + tot_roles, D1)
        inv.mixers('Linv_mid', lambda z: (F_KEY, ('perp', nk(z))), inverse=True)
        inv.copies('-V', 'Y', lambda T: (F_KEY, ('tperp', T)))
        inv.mixers('L2', lambda z: D1)
        inv.injections('J2', 'X', lambda S: D1, side)
        inv.gate('R2', allX + tot_roles, D1)
        inv.mixers('L2inv', lambda z: D1, inverse=True)
    return inv
