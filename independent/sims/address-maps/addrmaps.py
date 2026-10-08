"""Independent implementation of the compact-control packed address maps.

Source: notes/compact-control-movement.tex (identical text in the 05-layers hunk
of patches/compact-control-34.patch), repository CrocSwap/integer-mult-bounds
at 6e56487.  Written from the text, not from scripts/audit_compact_controls.py.

All functions work on Python ints (any width) and on numpy int64 arrays
(vectorised exhaustive runs, total width <= 62 bits per field).

State: dict mapping *physical positions* to the integer currently stored
there.  Positions: 'x','y' (slots, fK bits) and 'u','t','b' (compact fields,
nG bits).  Swaps exchange contents of two positions; a rotation replaces the
target position by (target + offset(controls)) mod 2^width.

Parameters
  K   chunk width, f slot chunks, n=f-1, rho in [0,K), j_i = rho + i K
  G   digit width, B = 2^G; compact fields have n radix-B digits
"""
from fractions import Fraction


class Params:
    def __init__(self, f, K, rho, G):
        assert f >= 2 and K >= 1 and 0 <= rho < K and G >= 1
        self.f, self.K, self.rho, self.G = f, K, rho, G
        self.n = f - 1
        self.B = 1 << G
        self.W_slot = f * K
        self.W_cmp = self.n * G
        self.j = [rho + i * K for i in range(f)]   # selected positions

    def width(self, pos):
        return self.W_slot if pos in ('x', 'y') else self.W_cmp

    def __repr__(self):
        return f"(f={self.f},K={self.K},rho={self.rho},G={self.G})"


# ---------------------------------------------------------------- helpers
def bit(v, pos):
    return (v >> pos) & 1


def digit(P, v, i):
    return (v >> (i * P.G)) & (P.B - 1)


def segment(P, y, i):
    """Segment [j_i, j_i+K) of y, i < n."""
    return (y >> P.j[i]) & ((1 << P.K) - 1)


def radixB(P, coefs):
    """sum_i c_i B^i  (signed integers allowed)."""
    s = 0
    for i, c in enumerate(coefs):
        s = s + c * (1 << (i * P.G))
    return s


def at_selected(P, coefs):
    """sum_i c_i 2^{j_i} over the low n selected positions."""
    s = 0
    for i, c in enumerate(coefs):
        s = s + c * (1 << P.j[i])
    return s


# ---------------------------------------------------------------- program
# Each op: ('swap', p, q) or
#          ('rot', target, controls, offset_fn, label)
# offset_fn(P, state) -> (offset_integer, coefficient list, kind)
# kind 'seg' : offset = sum c_i 2^{j_i} on y ; kind 'dig' : sum c_i B^i on b.
# Offsets read ONLY the listed control positions (checked dynamically below).

def _z_x(P, st):
    return [bit(st['x'], P.j[i]) for i in range(P.n)]


def _z_u(P, st):
    return [digit(P, st['u'], i) & 1 for i in range(P.n)]   # "u_i mod 2"


def make_program(late, packing='radixB'):
    """Ops in chronological order, following the text literally.

    packing='radixB' : "packed selected bits" = sum bit_i B^i  (reading A)
    packing='binary' : "packed selected bits" = sum bit_i 2^i  (reading B,
                       only for the t-loads, where the text does not say
                       radix-B explicitly)
    """
    def pk(P, bits):
        if packing == 'radixB':
            return radixB(P, bits)
        return sum(b_ * (1 << i) for i, b_ in enumerate(bits))

    ops = []

    def four_step(zsrc):
        zf = _z_x if zsrc == 'x' else _z_u

        # (1) v <- v + 2 z w : rotation of y, offset sum 2 x_{j_i} t_i 2^{j_i}
        def off1(P, st, zf=zf):
            z = zf(P, st)
            c = [2 * z[i] * digit(P, st['t'], i) for i in range(P.n)]
            return at_selected(P, c), c, 'seg'
        ops.append(('rot', 'y', (zsrc, 't'), off1, '(1) y += 2 z t'))

        # (2) w <- w + (v mod 2): swap t,b ; rotate back field by packed
        #     selected bits of the current y ; swap back
        def off2(P, st):
            c = [bit(st['y'], P.j[i]) for i in range(P.n)]
            return pk(P, c), c, 'dig'
        ops.append(('swap', 't', 'b'))
        ops.append(('rot', 'b', ('y',), off2, '(2) t += y_sel'))
        ops.append(('swap', 't', 'b'))

        # (3) v <- v + z (1 - 2 w): offset sum x_{j_i}(1-2t_i)2^{j_i}
        def off3(P, st, zf=zf):
            z = zf(P, st)
            c = [z[i] * (1 - 2 * digit(P, st['t'], i)) for i in range(P.n)]
            return at_selected(P, c), c, 'seg'
        ops.append(('rot', 'y', (zsrc, 't'), off3, '(3) y += z(1-2t)'))

        # (4) w <- w - ((v mod 2) xor z): minus packed bits y_{j_i} xor z_i
        def off4(P, st, zf=zf):
            z = zf(P, st)
            c = [-(bit(st['y'], P.j[i]) ^ z[i]) for i in range(P.n)]
            return pk(P, c), c, 'dig'
        ops.append(('swap', 't', 'b'))
        ops.append(('rot', 'b', ('y', zsrc), off4, '(4) t -= y_sel ^ z'))
        ops.append(('swap', 't', 'b'))

    def load(sign):
        # swap u,b ; rotate back field by +-(packed radix-B selected bits of x)
        def offl(P, st, sign=sign):
            c = [sign * bit(st['x'], P.j[i]) for i in range(P.n)]
            return radixB(P, c), c, 'dig'
        ops.append(('swap', 'u', 'b'))
        ops.append(('rot', 'b', ('x',), offl, 'load u' if sign > 0 else 'unload u'))
        ops.append(('swap', 'u', 'b'))

    if not late:
        four_step('x')
    else:
        four_step('u')
        load(+1)
        four_step('u')
        load(-1)
    return ops


# ---------------------------------------------------------------- execution
def _guarded(st, allowed):
    """A view of the state that raises if an offset reads a non-control."""
    class View(dict):
        def __getitem__(self, k):
            if k not in allowed:
                raise KeyError(f"offset read non-control position {k}")
            return dict.__getitem__(self, k)
    return View(st)


def run(P, state, ops, hook=None):
    st = dict(state)
    for op in ops:
        if op[0] == 'swap':
            _, p, q = op
            st[p], st[q] = st[q], st[p]
        else:
            _, tgt, ctrls, fn, _lbl = op
            off, coefs, kind = fn(P, _guarded(st, ctrls))
            mod = 1 << P.width(tgt)
            st[tgt] = (st[tgt] + off) % mod
            if hook:
                hook(op, st, coefs, kind)
    return st


def run_inverse(P, state, ops):
    """S^{-1}: reverse order; each inverse offset evaluated on the current
    controls at that point of the reversed sequence (the text's reading)."""
    st = dict(state)
    for op in reversed(ops):
        if op[0] == 'swap':
            _, p, q = op
            st[p], st[q] = st[q], st[p]
        else:
            _, tgt, ctrls, fn, _lbl = op
            off, _, _ = fn(P, _guarded(st, ctrls))
            st[tgt] = (st[tgt] - off) % (1 << P.width(tgt))
    return st


def run_inverse_naive(P, state, ops):
    """Alternative (rejected) reading: every inverse offset evaluated on the
    controls of the final address q, not on the current inverse controls."""
    q = dict(state)
    st = dict(state)
    # offsets must be computed on the layout current at that op, so track
    # only the swap permutation but read values from q
    loc = {k: k for k in state}            # logical content -> position (unused)
    for op in reversed(ops):
        if op[0] == 'swap':
            _, p, r = op
            st[p], st[r] = st[r], st[p]
        else:
            _, tgt, ctrls, fn, _lbl = op
            off, _, _ = fn(P, q)
            st[tgt] = (st[tgt] - off) % (1 << P.width(tgt))
    return st


def ideal(P, state):
    """T: y_{j_i} ^= x_{j_i} for the low n selected positions; all else fixed."""
    m = 0
    for i in range(P.n):
        m = m + (bit(state['x'], P.j[i]) << P.j[i])
    out = dict(state)
    out['y'] = state['y'] ^ m
    return out


def top_xor(P, state):
    """Elementary two-bit XOR at the omitted highest position j_n."""
    out = dict(state)
    out['y'] = state['y'] ^ (bit(state['x'], P.j[P.n]) << P.j[P.n])
    return out


def full_ideal(P, state):
    m = 0
    for i in range(P.f):
        m = m + (bit(state['x'], P.j[i]) << P.j[i])
    out = dict(state)
    out['y'] = state['y'] ^ m
    return out


def bad(P, state, late):
    """Bad predicate exactly as written:
    some t digit = B-1, or some target guard fails 2B <= g_i < 2^{K-1}-2B,
    or (later source) some u digit = B-1.  g_i = floor(segment_i / 2)."""
    B = P.B
    res = 0
    for i in range(P.n):
        res = res | (digit(P, state['t'], i) == B - 1)
        g = segment(P, state['y'], i) >> 1
        res = res | (g < 2 * B) | (g >= (1 << (P.K - 1)) - 2 * B)
        if late:
            res = res | (digit(P, state['u'], i) == B - 1)
    return res


def delta(P, late):
    """delta = min{1, n(2*2^-G + 8*2^{G-K})}; earlier source drops the 2."""
    a = 2 if late else 1
    return min(Fraction(1), P.n * (Fraction(a, P.B) + Fraction(8 * P.B, 1 << P.K)))


def repaired(P, state, ops, late):
    """S followed by deterministic repair of the bad records (destination
    T(S^{-1} q) for each current bad q), then the top-bit XOR."""
    out = run(P, state, ops)
    if bad(P, out, late):
        out = ideal(P, run_inverse(P, out, ops))
    return top_xor(P, out)
