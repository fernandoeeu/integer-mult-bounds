"""One invocation of a complex motif as a gate list with frames.

Frames are written in the factored form of the upstream stage decomposition
  D(Bp, Pp) = ((B (x) Bp) _|_ (P (x) Pp)) (x) Q,   Bp, Pp subspaces of F,
so D_0 = D(F,0), D_1 = D(F,F), D_U = D(F,U), physical Y line B(x)<t> =
D(<t>,0), incoming X data A(x)<t> = D(<t>,<t>), outgoing Y = D(F, t^perp).
The F-level checker validates both factors of every edge; tensor.py then
re-checks small cases with the actual subspaces of F^{(x)3}.

Wires: X_T = T, Y_T = v + T, centers 2v..2v+nc-1, roles after that.
"""
from f2 import Space, perp, residual, nondegenerate, nonalternating, orthonormal_basis, check_orthonormal

F_KEY = ('F',)
Z_KEY = ('0',)


class Labels:
    def __init__(self, C, node_label):
        self.C = C
        self.h = C.h
        self.node_label = node_label  # fn(key) -> Space
        self.cache = {}

    def space(self, key):
        sp = self.cache.get(key)
        if sp is not None:
            return sp
        h = self.h
        k = key[0]
        if k == 'F':
            sp = Space(h, [1 << i for i in range(h)])
        elif k == '0':
            sp = Space(h)
        elif k == 'line':
            sp = Space(h, [self.C.T[key[1]]])
        elif k == 'tperp':
            sp = perp(Space(h, [self.C.T[key[1]]]))
        elif k == 'perp':
            sp = perp(self.space(key[1]))
        else:
            sp = self.node_label(key)
        self.cache[key] = sp
        return sp


def node_key(C, z):
    if C.kind[z] == 'in':
        return ('line', C.args[z])
    return C.label[z]


class Invocation:
    """Gate list for one invocation; built by a recipe."""

    def __init__(self, C, roles, n_center):
        self.C, self.R = C, roles
        v = C.v
        self.v = v
        self.nc = n_center
        self.role0 = 2 * v + n_center
        self.nw = self.role0 + roles.n_roles
        self.gates = []  # (tag, wires tuple, (Bkey, Pkey))

    def X(self, T):
        return T

    def Y(self, T):
        return self.v + T

    def role(self, r):
        return self.role0 + r

    def gate(self, tag, wires, frame):
        self.gates.append((tag, tuple(wires), frame))

    # common pieces ---------------------------------------------------
    def mixers(self, tag, frame_of, inverse=False):
        C, R = self.C, self.R
        order = R.order if not inverse else list(reversed(R.order))
        for z in order:
            p, s, fan = R.gate[z]
            self.gate(tag, [self.role(p), self.role(s)] + [self.role(f) for f in fan], frame_of(z))

    def copies(self, tag, bank, frame_of):
        for T in range(self.v):
            w = self.X(T) if bank == 'X' else self.Y(T)
            self.gate(tag, [w] + [self.role(r) for r in self.R.slot_roles[T]], frame_of(T))

    def injections(self, tag, bank, frame_of, outputs_filter=None):
        C, R = self.C, self.R
        per = {}
        for k, (z, t, c) in enumerate(C.outputs):
            if outputs_filter and not outputs_filter(t):
                continue
            per.setdefault(t, []).append(R.out_role[k])
        for S in range(self.v):
            w = self.X(S) if bank == 'X' else self.Y(S)
            self.gate(tag, [w] + [self.role(r) for r in per.get(S, [])], frame_of(S))


def walk(inv):
    """Sequence of frames seen by every wire, in time order."""
    seq = [[] for _ in range(inv.nw)]
    for gi, (tag, wires, fr) in enumerate(inv.gates):
        for w in wires:
            seq[w].append((fr, tag))
    return seq


class EdgeChecker:
    def __init__(self, labels):
        self.L = labels
        self.res_cache = {}
        self.n_res = 0

    def residual_info(self, k1, k2):
        """Residual of Space(k1) -> Space(k2): returns (sign, dim, ok, why).
        sign +1 increase, -1 decrease, 0 equal; ok means comparable,
        both nondegenerate, residual zero or with a verified orthonormal basis."""
        key = (k1, k2)
        r = self.res_cache.get(key)
        if r is not None:
            return r
        U, V = self.L.space(k1), self.L.space(k2)
        if not nondegenerate(U) or not nondegenerate(V):
            r = (0, 0, False, 'degenerate label')
        elif V.contains_space(U):
            sign = 1 if V.dim() > U.dim() else 0
            r = self._res(U, V, sign)
        elif U.contains_space(V):
            r = self._res(V, U, -1)
        else:
            r = (0, 0, False, 'incomparable')
        self.res_cache[key] = r
        return r

    def _res(self, small, big, sign):
        E = residual(small, big)
        self.n_res += 1
        if E.dim() == 0:
            return (sign, 0, True, '')
        if not nondegenerate(E):
            return (sign, E.dim(), False, 'degenerate residual')
        ob = orthonormal_basis(E)
        if ob is None:
            return (sign, E.dim(), False, 'alternating residual (no norm-one vector)')
        if not check_orthonormal(ob, E):
            return (sign, E.dim(), False, 'orthonormal construction failed')
        return (sign, E.dim(), True, '')

    def edge(self, f1, f2, stage):
        """Check a frame edge D(B1,P1) -> D(B2,P2) at stage j.
        Returns (ok, signed_full_dim_change, abs_change, why)."""
        (b1, p1), (b2, p2) = f1, f2
        dimB = self.L.h ** (stage - 1) - 1  # dim of B = P^perp in A
        sb, db, okb, whyb = self.residual_info(b1, b2) if dimB > 0 else (0, 0, True, '')
        sp, dp, okp, whyp = self.residual_info(p1, p2)
        if not okb:
            return False, 0, 0, 'B-part: ' + whyb
        if not okp:
            return False, 0, 0, 'P-part: ' + whyp
        if sb * sp < 0:
            return False, 0, 0, 'B and P parts change in opposite directions'
        sign = sb or sp
        ch = dimB * db + dp
        return True, sign * ch, ch, ''


def check_invocation(inv, labels, stage, sources, sinks, aux_sink_full=True, ec=None):
    """sources/sinks: dict wire -> frame for data wires (and centers).
    Aux roles: source D(0,0); sink: full space (last frame must be D_1).
    Returns a report dict."""
    if ec is None:
        ec = EdgeChecker(labels)
    seq = walk(inv)
    h = labels.h
    m = h ** 3
    fails = []
    tot_abs = 0
    tot_signed = 0
    dec = []
    n_edges = 0
    for w in range(inv.nw):
        frames = [f for f, _ in seq[w]]
        if w >= inv.role0 or (2 * inv.v <= w < inv.role0):
            src = (Z_KEY, Z_KEY)
        else:
            src = sources[w]
        chain = [src] + frames
        if w in sinks:
            chain.append(sinks[w])
        for i in range(len(chain) - 1):
            ok, sch, ach, why = ec.edge(chain[i], chain[i + 1], stage)
            n_edges += 1
            if not ok:
                fails.append((w, i, chain[i], chain[i + 1], why))
                continue
            tot_abs += ach
            tot_signed += sch
            if sch < 0:
                dec.append((w, i, -sch, chain[i], chain[i + 1]))
        if w not in sinks:
            # aux or center wire: sink is the full space F^{(x)3}
            last = chain[-1]
            if last != (F_KEY, F_KEY):
                fails.append((w, 'last', last, 'full', 'last frame is not D_1'))
            else:
                ch = m - h ** stage
                tot_abs += ch
                tot_signed += ch
    return dict(fails=fails, tot_abs=tot_abs, tot_signed=tot_signed, dec=dec,
                n_edges=n_edges, n_residuals=ec.n_res, checker=ec)


def data_terminals(inv):
    """Incoming/outgoing prescribed labels for data wires at any stage."""
    src, snk = {}, {}
    for T in range(inv.v):
        src[inv.X(T)] = (('line', T), ('line', T))
        snk[inv.X(T)] = (F_KEY, F_KEY)
        src[inv.Y(T)] = (('line', T), Z_KEY)
        snk[inv.Y(T)] = (F_KEY, ('tperp', T))
    return src, snk
