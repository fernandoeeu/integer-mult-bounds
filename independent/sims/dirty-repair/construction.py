"""Independent implementation of the compact dirty-control selected-bit
addition and its deterministic exceptional repair, as written in
notes/compact-control-movement.tex (repo CrocSwap/integer-mult-bounds @ 6e56487).

Written from the text only; it does not import or copy the repository's
scripts.

Model
-----
An address is a tuple of field values over a physical field list in
lexicographic order (first field most significant).  Physical slots are
named; the *content* of a slot can move by swaps.  Two primitive operations,
both bijections of the complete rectangle:

  swap(A, B)                 exchange the contents of equal-width slots A, B
  rot(T, reads, off)         T <- T + off(state) mod 2^width(T), where off
                             reads only the slots in `reads`; every slot in
                             `reads` must physically precede T (checked).

All functions work both on Python ints (one address, arbitrary precision)
and on numpy int64 arrays (a vector of addresses), as long as every field
fits in 62 bits for the numpy case.

Bits are numbered from the least significant bit (upstream convention,
05-layers.tex, lem:packed-selected-bit-rectangle).
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable

try:
    import numpy as np
except ImportError:  # pragma: no cover
    np = None


def _mod(v, m):
    # Python % and numpy np.mod both return a value in [0, m) for m > 0.
    return v % m


@dataclass
class Params:
    G: int          # radix exponent, B = 2^G
    K: int          # selected-position spacing
    f: int          # number of selected positions (slot width fK)
    rho: int        # offset of first selected position, 0 <= rho < K
    later: bool     # False: x precedes y (earlier source); True: y precedes x

    @property
    def n(self):
        return self.f - 1

    @property
    def B(self):
        return 1 << self.G

    @property
    def L(self):
        return self.f * self.K

    def j(self, i):
        return self.rho + i * self.K


@dataclass
class Layout:
    """Physical field order (most significant first) and widths."""
    order: list
    width: dict

    def index(self, name):
        return self.order.index(name)

    def precedes(self, a, b):
        return self.index(a) < self.index(b)


def default_layout(P: Params, front=("u", "t"), spectators=()):
    """Build a layout.  `front` gives the order of the two front compact
    fields; `spectators` is a list of (position_tag, name, width) where
    position_tag is an index into the core list at which to insert."""
    nG = P.n * P.G
    slots = ["y", "x"] if P.later else ["x", "y"]
    core = list(front) + slots + ["b"]
    width = {"u": nG, "t": nG, "b": nG, "x": P.L, "y": P.L}
    order = list(core)
    # insert spectators from the back so indices stay meaningful
    for pos, name, w in sorted(spectators, key=lambda s: -s[0]):
        order.insert(pos, name)
        width[name] = w
    return Layout(order, width)


# ---------------------------------------------------------------- operations
@dataclass
class Op:
    kind: str                     # 'swap' or 'rot'
    a: str = ""
    b: str = ""
    target: str = ""
    reads: tuple = ()
    off: Callable = None
    label: str = ""


def bit(v, k):
    return (v >> k) & 1


def digit(v, i, G):
    return (v >> (G * i)) & ((1 << G) - 1)


def build_ops(P: Params, layout: Layout, variant: str = "text"):
    """Return the operation list S for the selected positions j_0..j_{n-1}.

    variant:
      'text'  - as written: step-3 offset uses the current temporary digits.
    """
    G, B, n = P.G, P.B, P.n
    js = [P.j(i) for i in range(n)]

    def packed_y(st):
        y = st["y"]
        return sum(bit(y, js[i]) << (G * i) for i in range(n))

    def earlier(ctrl):
        """Earlier-source construction with control bits z_i read from
        physical slot `ctrl` ('x': bit j_i of x; 'u': parity of digit i)."""
        if ctrl == "x":
            z = lambda st, i: bit(st["x"], js[i])
        else:
            z = lambda st, i: bit(st["u"], G * i)  # u_i mod 2

        def off1(st):  # v <- v + 2 z w
            t = st["t"]
            return sum((2 * z(st, i) * digit(t, i, G)) << js[i] for i in range(n))

        def off2(st):  # w <- w + (v mod 2): back field += packed bits of current y
            return packed_y(st)

        def off3(st):  # v <- v + z (1 - 2 w)   (w = current t digit)
            t = st["t"]
            return sum(z(st, i) * (1 - 2 * digit(t, i, G)) * (1 << js[i]) for i in range(n))

        def off4(st):  # w <- w - ((v mod 2) xor z)
            y = st["y"]
            return -sum((bit(y, js[i]) ^ z(st, i)) << (G * i) for i in range(n))

        return [
            Op("rot", target="y", reads=(ctrl, "t"), off=off1, label=f"E[{ctrl}].1 y+=2zw"),
            Op("swap", a="t", b="b", label="swap t,b"),
            Op("rot", target="b", reads=("y",), off=off2, label=f"E[{ctrl}].2 w+=v mod 2"),
            Op("swap", a="t", b="b", label="swap t,b"),
            Op("rot", target="y", reads=(ctrl, "t"), off=off3, label=f"E[{ctrl}].3 y+=z(1-2w)"),
            Op("swap", a="t", b="b", label="swap t,b"),
            Op("rot", target="b", reads=("y", ctrl), off=off4, label=f"E[{ctrl}].4 w-=(v mod2)^z"),
            Op("swap", a="t", b="b", label="swap t,b"),
        ]

    if n == 0:
        return []
    if not P.later:
        return earlier("x")

    def load(sign):
        def off(st):
            x = st["x"]
            return sign * sum(bit(x, js[i]) << (G * i) for i in range(n))
        return [
            Op("swap", a="u", b="b", label="swap u,b"),
            Op("rot", target="b", reads=("x",), off=off, label=f"load u {'+' if sign > 0 else '-'}x"),
            Op("swap", a="u", b="b", label="swap u,b"),
        ]

    return earlier("u") + load(+1) + earlier("u") + load(-1)


def check_order(ops, layout: Layout):
    """Every rotation reads only slots that physically precede its target,
    and swapped slots have equal width."""
    for op in ops:
        if op.kind == "rot":
            for r in op.reads:
                assert r != op.target, op.label
                assert layout.precedes(r, op.target), (op.label, r, op.target, layout.order)
        else:
            assert layout.width[op.a] == layout.width[op.b], op.label


def apply_op(op, st, layout, inverse=False):
    st = dict(st)
    if op.kind == "swap":
        st[op.a], st[op.b] = st[op.b], st[op.a]
    else:
        m = 1 << layout.width[op.target]
        off = op.off(st)  # computed from current controls (target not read)
        if inverse:
            off = -off
        st[op.target] = _mod(st[op.target] + off, m)
    return st


def run(ops, st, layout):
    for op in ops:
        st = apply_op(op, st, layout)
    return st


def run_inverse(ops, st, layout):
    """S^{-1}: reverse order, negated offsets evaluated on the current
    (inverse-time) controls."""
    for op in reversed(ops):
        st = apply_op(op, st, layout, inverse=True)
    return st


def run_inverse_final_controls(ops, st, layout):
    """A WRONG reading, for contrast only: all inverse offsets evaluated on
    the controls of the address before inversion started."""
    frozen = dict(st)
    for op in reversed(ops):
        if op.kind == "swap":
            st = apply_op(op, st, layout, inverse=True)
        else:
            m = 1 << layout.width[op.target]
            st = dict(st)
            st[op.target] = _mod(st[op.target] - op.off(frozen), m)
    return st


# ----------------------------------------------------------- ideal maps / bad
def ideal_T(P: Params, st):
    """T: y_{j_i} ^= x_{j_i} for i < n; every other field and bit fixed."""
    st = dict(st)
    y = st["y"]
    for i in range(P.n):
        y = y ^ (bit(st["x"], P.j(i)) << P.j(i))
    st["y"] = y
    return st


def full_xor(P: Params, st):
    """The required operation: y_{j_i} ^= x_{j_i} for all 0 <= i < f."""
    st = dict(st)
    y = st["y"]
    for i in range(P.f):
        y = y ^ (bit(st["x"], P.j(i)) << P.j(i))
    st["y"] = y
    return st


def highest_xor(P: Params, st):
    """Elementary two-bit XOR on the omitted highest position j_n."""
    st = dict(st)
    jn = P.j(P.n)
    st["y"] = st["y"] ^ (bit(st["x"], jn) << jn)
    return st


def guard_values(P: Params, y, i):
    seg = (y >> P.j(i)) & ((1 << P.K) - 1)
    return seg >> 1


def is_bad(P: Params, st):
    """Bad set as written: some t digit = B-1, or some guard
    2B <= g_i < 2^{K-1} - 2B fails, or (later source) some u digit = B-1."""
    B = P.B
    lo, hi = 2 * B, (1 << (P.K - 1)) - 2 * B
    bad = False
    for i in range(P.n):
        g = guard_values(P, st["y"], i)
        bad = bad | (digit(st["t"], i, P.G) == B - 1) | (g < lo) | (g >= hi)
        if P.later:
            bad = bad | (digit(st["u"], i, P.G) == B - 1)
    return bad


def rank(layout: Layout, st):
    """Lexicographic rank (first field most significant)."""
    r = 0
    for name in layout.order:
        r = (r << layout.width[name]) | st[name]
    return r


def repaired(P, ops, layout, st_initial, inv=run_inverse):
    """Full procedure on one address (or vector): run S, then for every
    record now at a bad address q, move it to T(S^{-1} q); then do the
    elementary XOR on the highest selected position.  Returns
    (final, current_after_S, bad_now, destination)."""
    cur = run(ops, st_initial, layout)
    bad_now = is_bad(P, cur)
    dest = ideal_T(P, inv(ops, cur, layout))
    return cur, bad_now, dest
