"""Exact scalar simulation of the motifs with arbitrary (dirty) scratch.

All gate coefficients are real dyadic (0, +-1, +-1/2, +-1/4), so the action on
Z[i,1/2] splits into independent real and imaginary parts; we simulate both
parts as separate exact integer runs.  Values are integers scaled by 2^SHIFT;
every multiplication by 1/2 or 1/4 asserts exact divisibility, so the run is
exact dyadic arithmetic (an assertion fires otherwise).  numpy int64 is used
with an explicit overflow guard.
"""
import numpy as np
from fractions import Fraction

SHIFT = 24
LIM = 1 << 60


def scale(arr, c):
    """Multiply int array by an exact dyadic Fraction c."""
    num, den = c.numerator, c.denominator
    assert den & (den - 1) == 0
    out = arr * num
    if den > 1:
        assert not (out % den).any(), "inexact halving"
        out = out // den
    assert np.abs(out).max(initial=0) < LIM
    return out


class Motif:
    """Wraps a circuit, its roles, and the PR-specific central/scatter maps."""

    def __init__(self, C, R, kind):
        self.C, self.R, self.kind = C, R, kind
        v = C.v
        self.v = v
        h = C.h
        # injection lists per target
        self.inj = [[] for _ in range(v)]
        self.tot = {}
        for k, (z, t, c) in enumerate(C.outputs):
            if isinstance(t, tuple):
                self.tot[t] = R.out_role[k]
            else:
                self.inj[t].append((R.out_role[k], c))
        if kind == 'pr3':
            self.nc = h + 1
        else:
            self.nc = 0
            from pr4 import scatter_rows
            self.scat = scatter_rows(C)

    # gates on arrays of shape (n, cols)
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

    def G(self, X, Cw, sign):
        h, T = self.C.h, self.C.T
        for i in range(h):
            for ti, t in enumerate(T):
                if t >> i & 1:
                    Cw[i] += sign * X[ti]
        Cw[h] += sign * X.sum(axis=0)

    def Rc(self, Y, Cw, sign):
        h, T = self.C.h, self.C.T
        for si, s in enumerate(T):
            acc = -Cw[h]
            for i in range(h):
                if s >> i & 1:
                    acc = acc + Cw[i]
            Y[si] += sign * scale(acc, Fraction(1, 2))

    def Rt(self, Y, Z, sign):
        for si in range(self.v):
            for tag, c in self.scat[si].items():
                Y[si] += sign * scale(Z[self.tot[tag]], c)

    def forward(self, X, Y, Z, Cw):
        """Logical source X, target Y (physical names irrelevant here)."""
        if self.kind == 'pr3':
            seq = ['L', '-J', 'Li', '-R', 'V', 'G', 'R', 'L', 'J', 'Li', 'Gi', 'Vi']
        else:
            seq = ['L', '-Rt', '-J', 'Li', 'V', 'L', 'Rt', 'J', 'Li', '-V']
        self.run(seq, X, Y, Z, Cw)

    def inverse(self, X, Y, Z, Cw):
        """Inverse of forward with logical source X, target Y: Y -= X."""
        if self.kind == 'pr3':
            seq = ['V', 'G', 'L', '-J', 'Li', '-R', 'Gi', 'Vi', 'R', 'L', 'J', 'Li']
        else:
            seq = ['V', 'L', '-J', '-Rt', 'Li', '-V', 'L', 'J', 'Rt', 'Li']
        self.run(seq, X, Y, Z, Cw)

    def run(self, seq, X, Y, Z, Cw):
        for op in seq:
            if op == 'L':
                self.mix(Z)
            elif op == 'Li':
                self.mix(Z, True)
            elif op in ('J', '-J'):
                self.J(Y, Z, -1 if op[0] == '-' else 1)
            elif op in ('V', '-V', 'Vi'):
                self.V(X, Z, 1 if op == 'V' else -1)
            elif op in ('G', 'Gi'):
                self.G(X, Cw, 1 if op == 'G' else -1)
            elif op in ('R', '-R'):
                self.Rc(Y, Cw, -1 if op[0] == '-' else 1)
            elif op in ('Rt', '-Rt'):
                self.Rt(Y, Z, -1 if op[0] == '-' else 1)
            else:
                raise ValueError(op)
            for arr in (X, Y, Z, Cw):
                if arr is not None and arr.size:
                    assert np.abs(arr).max() < LIM


def rand(rng, shape):
    return rng.integers(-2**20, 2**20, size=shape, dtype=np.int64) << SHIFT


def single_invocation(M, cols=4, seed=1):
    """Forward: y += x; inverse: y -= x; scratch restored; all exact."""
    rng = np.random.default_rng(seed)
    v, nr, nc = M.v, M.R.n_roles, M.nc
    res = {}
    for name, fn, sgn in (('forward', M.forward, 1), ('inverse', M.inverse, -1)):
        X, Y = rand(rng, (v, cols)), rand(rng, (v, cols))
        Z, Cw = rand(rng, (nr, cols)), rand(rng, (nc, cols))
        X0, Y0, Z0, C0 = X.copy(), Y.copy(), Z.copy(), Cw.copy()
        fn(X, Y, Z, Cw)
        res[name] = dict(target=bool((Y == Y0 + sgn * X0).all()), source=bool((X == X0).all()),
                         scratch=bool((Z == Z0).all()), centers=bool((Cw == C0).all()))
    # basis vectors with zero and dirty scratch: column k = e_k
    if v <= 400:
        X = np.zeros((v, v), dtype=np.int64)
        for k in range(v):
            X[k, k] = 1 << SHIFT
        Y = np.zeros((v, v), dtype=np.int64)
        Z = rand(rng, (nr, v))
        Cw = rand(rng, (nc, v))
        Z0, C0 = Z.copy(), Cw.copy()
        M.forward(X, Y, Z, Cw)
        res['basis'] = bool((Y == X).all() and (Z == Z0).all() and (Cw == C0).all())
    return res


def three_stage(M, shared=False, seed=2):
    """Full exchange (X,Y) -> (-Y,X) over T^3 with dirty, per-invocation
    scratch.  shared=True: stage-1 bank (A,B) is the stage-3 bank (B,pi(A))."""
    rng = np.random.default_rng(seed)
    C = M.C
    v, nr, nc, h = M.v, M.R.n_roles, M.nc, C.h
    X = rand(rng, (v, v, v))
    Y = rand(rng, (v, v, v))
    X0, Y0 = X.copy(), Y.copy()
    banks = {j: (rand(rng, (nr, v, v)), rand(rng, (nc, v, v))) for j in (1, 2, 3)}
    if shared:
        pi = pi_map(C)
        # bank3[:, B, piA] = bank1[:, A, B]
        Z1 = banks[1][0]
        Z3 = np.empty_like(Z1)
        for A in range(v):
            for B in range(v):
                Z3[:, B, pi[A]] = Z1[:, A, B]
        banks[3] = (Z3, banks[1][1])
    init = {j: (banks[j][0].copy(), banks[j][1].copy()) for j in banks}

    def stage(j, fn, src, dst):
        Z, Cw = banks[j]
        # move axis j-1 to front, flatten the other two (in order)
        s = np.moveaxis(src, j - 1, 0).reshape(v, v * v)
        d = np.moveaxis(dst, j - 1, 0).reshape(v, v * v)
        Zf = Z.reshape(nr, v * v)
        Cf = Cw.reshape(nc, v * v)
        fn(s, d, Zf, Cf)
        return (np.moveaxis(s.reshape(v, v, v), 0, j - 1),
                np.moveaxis(d.reshape(v, v, v), 0, j - 1))

    X, Y = stage(1, M.forward, X, Y)
    after1 = (banks[1][0].copy(), banks[1][1].copy())
    Y, X = stage(2, M.inverse, Y, X)
    if shared:
        # stage-3 bank must hold the restored stage-1 values
        Z1f = after1[0]
        Z3 = banks[3][0]
        ok_join = all((Z3[:, B, pi[A]] == Z1f[:, A, B]).all() for A in range(v) for B in range(v))
    X, Y = stage(3, M.forward, X, Y)
    out = dict(exchange=bool((X == -Y0).all() and (Y == X0).all()))
    out['restored'] = all((banks[j][0] == init[j][0]).all() and (banks[j][1] == init[j][1]).all()
                          for j in (1, 2, 3))
    if shared:
        out['join_values'] = ok_join
    return out


def pi_map(C):
    """Pair adjacent ground points (0,1),(2,3),...; pi flips each point."""
    out = []
    for t in C.T:
        u = 0
        for p in range(C.h):
            if t >> p & 1:
                u |= 1 << (p ^ 1)
        out.append(C.tidx[u])
    return out
