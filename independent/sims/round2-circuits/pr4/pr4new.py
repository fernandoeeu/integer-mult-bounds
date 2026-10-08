"""PR 4 head 8c225e6: PR 3's compressed complex side circuit with retained
exclusion totals E_i (i < h-1) and C_*, the (|S cap T|-1)/2 central scatter
split into h-5 normalized passes, and the L,-R,-J,L^-1,V,L,R,J,L^-1,-V wrapper.

Written from docs/research/shared-retained-complex.md at 8c225e6. The PR 3
part is the earlier independent reconstruction (pr3.py, written from
notes/complex-circuit-construction.tex of PR 3, not from its Python).
"Retain the existing nodes E_i = sum_{T not containing i} x_T" is read as
the top-level exclusion sums tri([h])[{i}] and tri([h])[{}] of PR 3's
disjoint routine, interned by support with the rest of the disjoint family.
"""
from fractions import Fraction
from pr3 import PR3Builder, label_space  # noqa: F401  (label_space re-exported)
from network import Invocation, F_KEY, Z_KEY, node_key
import numpy as np
from scalar import scale, LIM

HALF = Fraction(1, 2)
D0 = (F_KEY, Z_KEY)
D1 = (F_KEY, F_KEY)


def build(h, retain=True, retain_last=False):
    B = PR3Builder(h)
    C = B.C
    real_prune = C.prune
    C.prune = lambda keep_extra=(): None
    B.build()
    if retain:
        ret = B.tri(list(range(h)), 1)
        idx = list(range(h - 1)) + ([h - 1] if retain_last else [])
        for i in idx:
            C.outputs.append((ret[frozenset([i])], ('tot', i), Fraction(1)))
        C.outputs.append((ret[frozenset()], ('tot', '*'), Fraction(1)))
    del C.prune
    real_prune()
    C.split_log = B.split_log
    return C


def scatter_passes(h, Smask, retain_last=False):
    """List of h-5 pass rows {tag: coeff} for target S (doc text)."""
    last = (Smask >> (h - 1)) & 1
    passes = []
    if not last:
        row = {('tot', '*'): Fraction(1)}
        for i in range(h - 1):
            if Smask >> i & 1:
                row[('tot', i)] = -HALF
        passes.append(row)
        passes += [{} for _ in range(h - 6)]
    else:
        row = {('tot', '*'): -HALF}
        for i in range(h - 1):
            if not Smask >> i & 1:
                row[('tot', i)] = HALF
        passes.append(row)
        passes += [{('tot', '*'): -HALF} for _ in range(h - 6)]
    return passes


def check_map(C):
    """(R + J) L V = I exactly, integer multiplicities, Fractions."""
    sup = C.supports()
    tot, side = {}, {}
    for z, t, c in C.outputs:
        if isinstance(t, tuple):
            tot[t] = sup[z]
        else:
            row = side.setdefault(t, {})
            for s, m in sup[z].items():
                row[s] = row.get(s, 0) + c * m
    h = C.h
    fails = []
    maxc = Fraction(0)
    for si, S in enumerate(C.T):
        acc = dict(side.get(si, {}))
        for p in scatter_passes(h, S):
            for tag, c in p.items():
                maxc = max(maxc, abs(c))
                for s, m in tot[tag].items():
                    acc[s] = acc.get(s, 0) + c * m
        for ti in range(C.v):
            want = 1 if ti == si else 0
            if acc.get(ti, 0) != want:
                fails.append((si, ti, acc.get(ti, 0)))
                if len(fails) > 10:
                    return False, fails, maxc
    return not fails, fails, maxc


def check_totals(C):
    sup = C.supports()
    h = C.h
    bad = []
    for z, t, c in C.outputs:
        if not isinstance(t, tuple):
            continue
        i = t[1]
        want = {k: 1 for k, T in enumerate(C.T) if i == '*' or not (T >> i) & 1}
        if sup[z] != want:
            bad.append(t)
    return bad


def invocation(C, R, reverse=False, variant=None):
    """Frames: doc text 'The grouped forward scatter uses the common low frame
    ... The reverse uses the common full frame followed by complemented
    mixing'; the rest as in PR 4's retained-complex note (early mixer,
    scatter and injection at D_0; middle D_U; injection at t^perp; late D_1)."""
    h = C.h
    inv = Invocation(C, R, n_center=0)
    v = C.v
    tot_role = {}
    for k, (z, t, c) in enumerate(C.outputs):
        if isinstance(t, tuple):
            tot_role[t] = inv.role(R.out_role[k])
    side = lambda t: not isinstance(t, tuple)
    nk = lambda z: node_key(C, z)
    last_targets = [S for S in range(v) if C.T[S] >> (h - 1) & 1]

    def passes(tag, bank, frame):
        W = inv.X if bank == 'X' else inv.Y
        inv.gate(tag + '#0', [W(S) for S in range(v)] + list(tot_role.values()), frame)
        for k in range(1, h - 5):
            inv.gate(tag + '#%d' % k, [W(S) for S in last_targets] + [tot_role['tot', '*']], frame)

    if not reverse:
        inv.mixers('L0', lambda z: D0)
        passes('-R0', 'Y', D0)
        inv.injections('-J0', 'Y', lambda S: D0, side)
        inv.mixers('L0inv', lambda z: D0, inverse=True)
        inv.copies('V', 'X', lambda T: (F_KEY, ('line', T)))
        inv.mixers('Lmid', lambda z: (F_KEY, nk(z)))
        if variant == 'J_before_R':
            inv.injections('J', 'Y', lambda S: (F_KEY, ('tperp', S)), side)
            passes('R', 'Y', D0)
        else:
            passes('R', 'Y', D0)
            inv.injections('J', 'Y', lambda S: (F_KEY, ('tperp', S)), side)
        inv.mixers('Llate_inv', lambda z: D1, inverse=True)
        inv.copies('-V', 'X', lambda T: D1)
    else:
        inv.copies('V', 'Y', lambda T: (('line', T), Z_KEY))
        inv.mixers('L', lambda z: D0)
        inv.injections('-J', 'X', lambda S: (F_KEY, ('line', S)), side)
        passes('-R', 'X', D1)
        inv.mixers('Linv_mid', lambda z: (F_KEY, ('perp', nk(z))) if variant != 'reverse_uncomplemented'
                   else (F_KEY, nk(z)), inverse=True)
        inv.copies('-V', 'Y', lambda T: (F_KEY, ('tperp', T)))
        inv.mixers('L2', lambda z: D1)
        inv.injections('J2', 'X', lambda S: D1, side)
        passes('R2', 'X', D1)
        inv.mixers('L2inv', lambda z: D1, inverse=True)
    return inv


class Motif:
    """Exact dyadic scalar simulation (real parts; all gate coefficients are
    real), arbitrary dirty scratch, the h-5 passes applied one at a time."""

    def __init__(self, C, R):
        self.C, self.R = C, R
        self.v = C.v
        self.nc = 0
        self.inj = [[] for _ in range(C.v)]
        self.tot = {}
        for k, (z, t, c) in enumerate(C.outputs):
            if isinstance(t, tuple):
                self.tot[t] = R.out_role[k]
            else:
                self.inj[t].append((R.out_role[k], c))
        self.passes = [scatter_passes(C.h, S) for S in C.T]
        self.max_coeff = max(abs(c) for ps in self.passes for p in ps for c in p.values())

    def mix(self, Z, inverse=False):
        R = self.R
        if not inverse:
            for z in R.order:
                p, s, fan = R.gate[z]
                Z[p] += Z[s]
                for f in fan:
                    Z[f] += Z[p]
        else:
            for z in reversed(R.order):
                p, s, fan = R.gate[z]
                for f in fan:
                    Z[f] -= Z[p]
                Z[p] -= Z[s]

    def J(self, Y, Z, sign):
        for S in range(self.v):
            for r, c in self.inj[S]:
                Y[S] += sign * scale(Z[r], c)

    def V(self, X, Z, sign):
        for T in range(self.v):
            for r in self.R.slot_roles[T]:
                Z[r] += sign * X[T]

    def Rt(self, Y, Z, sign, reverse_order=False):
        npass = len(self.passes[0])
        order = range(npass - 1, -1, -1) if reverse_order else range(npass)
        for k in order:
            for S in range(self.v):
                for tag, c in self.passes[S][k].items():
                    Y[S] += sign * scale(Z[self.tot[tag]], c)

    def forward(self, X, Y, Z, Cw=None):
        self.mix(Z); self.Rt(Y, Z, -1); self.J(Y, Z, -1); self.mix(Z, True)
        self.V(X, Z, 1)
        self.mix(Z); self.Rt(Y, Z, 1); self.J(Y, Z, 1); self.mix(Z, True)
        self.V(X, Z, -1)

    def inverse(self, X, Y, Z, Cw=None):
        """Reverse and invert the forward schedule (logical source X,
        target Y): V, L, -J, -R, L^-1, -V, L, J, R, L^-1."""
        self.V(X, Z, 1); self.mix(Z); self.J(Y, Z, -1); self.Rt(Y, Z, -1, True); self.mix(Z, True)
        self.V(X, Z, -1)
        self.mix(Z); self.J(Y, Z, 1); self.Rt(Y, Z, 1, True); self.mix(Z, True)
