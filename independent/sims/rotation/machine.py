"""Independent fixed-tape simulation of the two-piece controlled rotation
of lem:record-paid-rotation (notes/compact-control-movement.tex), written
from the text only.

Model (02-streams.tex conventions): an array on [L_0] x ... x [L_{k-1}],
lexicographic, first field most significant, one payload cell per address.
The target field index is `ti`, with range Q = L_ti. Fields before ti form
the prefix (controls and spectators); fields after ti form the suffix of
B = prod(L_{ti+1:}) cells per target block.

Every head move on every tape is counted, in three buckets:
  data    : input read, piece writes, piece reads, output writes, rewinds
  stream  : per-block and per-cell counters (suffix countdown, block
            countdown decrements, suffix-length reload per block)
  fiber   : per-fiber work (prefix counter advance and resets, control
            value counters, offset computation, piece-length initialisation)
"""

from dataclasses import dataclass, field


class Cost:
    def __init__(self):
        self.data = 0
        self.stream = 0
        self.fiber = 0
        self.offset_calls = 0
        self.offset_cost = 0
        self.max_offset_cost = 0
        self.copies = 0  # payload cell writes (piece + output)

    @property
    def total(self):
        return self.data + self.stream + self.fiber


class Counter:
    """Binary counter on its own track, LSB first, head parked at the LSB.

    Every operation walks the head and returns it; cost = 2 * cells visited
    (minimum 2 per operation for touching the LSB)."""

    def __init__(self, width):
        self.width = max(1, width)
        self.bits = [0] * self.width

    def load(self, value):
        """Copy `value` (from a local copy track) into the counter."""
        assert 0 <= value < (1 << self.width), (value, self.width)
        for j in range(self.width):
            self.bits[j] = (value >> j) & 1
        return 2 * self.width

    def value(self):
        return sum(b << j for j, b in enumerate(self.bits))

    def decrement(self):
        """Return (underflow, cost). Underflow means value was 0."""
        j = 0
        while j < self.width and self.bits[j] == 0:
            self.bits[j] = 1
            j += 1
        if j == self.width:
            return True, 2 * self.width
        self.bits[j] = 0
        return False, 2 * (j + 1)

    def increment(self):
        j = 0
        while j < self.width and self.bits[j] == 1:
            self.bits[j] = 0
            j += 1
        if j < self.width:
            self.bits[j] = 1
        return 2 * (min(j, self.width - 1) + 1)

    def read_bit(self, j):
        """Bit j and the cost of walking to it and back."""
        if j >= self.width:
            return 0, 2 * self.width
        return self.bits[j], 2 * (j + 1)


def bitlen(n):
    return max(1, int(n).bit_length())


@dataclass
class Layout:
    lengths: list          # field ranges
    ti: int                # target field index
    controls: list         # indices < ti
    names: list = field(default_factory=list)

    def __post_init__(self):
        assert 0 <= self.ti < len(self.lengths)
        for c in self.controls:
            assert c < self.ti, "control must precede target"
        if not self.names:
            self.names = [f"f{i}" for i in range(len(self.lengths))]

    @property
    def Q(self):
        return self.lengths[self.ti]

    @property
    def B(self):
        r = 1
        for L in self.lengths[self.ti + 1:]:
            r *= L
        return r

    @property
    def P(self):
        r = 1
        for L in self.lengths[:self.ti]:
            r *= L
        return r

    @property
    def V(self):
        return self.P * self.Q * self.B


class PrefixCounters:
    """Mixed-radix enumeration of the prefix fields: one countdown per field
    (reloaded from its local length copy on wrap) and, for each control
    field, an up-counter holding its current value."""

    def __init__(self, layout, cost):
        self.lay = layout
        self.cost = cost
        k = layout.ti
        self.cd = [Counter(bitlen(layout.lengths[i])) for i in range(k)]
        self.val = {c: Counter(bitlen(layout.lengths[c])) for c in layout.controls}
        for i in range(k):
            cost.fiber += self.cd[i].load(layout.lengths[i] - 1)
        for c in self.val:
            cost.fiber += self.val[c].load(0)

    def advance(self):
        """Advance to next prefix. Return False when enumeration ended."""
        i = self.lay.ti - 1
        while i >= 0:
            uf, c = self.cd[i].decrement()
            self.cost.fiber += c
            if i in self.val:
                if not uf:
                    self.cost.fiber += self.val[i].increment()
                else:
                    self.cost.fiber += self.val[i].load(0)
            if not uf:
                return True
            self.cost.fiber += self.cd[i].load(self.lay.lengths[i] - 1)
            i -= 1
        return False


def copy_blocks(src, src_pos, dst, nblocks, B, Qw, Bw, cost):
    """Copy nblocks blocks of B cells from src[src_pos:] to dst.
    Block countdown of width Qw and suffix countdown of width Bw."""
    if nblocks == 0:
        return src_pos
    bc = Counter(Qw)
    cost.fiber += bc.load(nblocks - 1)
    sc = Counter(Bw)
    while True:
        cost.stream += sc.load(B - 1)          # local suffix-length copy
        while True:
            dst.append(src[src_pos])
            src_pos += 1
            cost.data += 2                      # one read move, one write move
            cost.copies += 1
            uf, c = sc.decrement()
            cost.stream += c
            if uf:
                break
        uf, c = bc.decrement()
        cost.stream += c
        if uf:
            break
    return src_pos


def two_piece_rotation(layout, data, offset_fn):
    """Run the construction. offset_fn(ctrl_counters, layout) -> (int, cost)
    reads control values only through the counters. Returns (out, Cost,
    stats)."""
    cost = Cost()
    Q, B = layout.Q, layout.B
    Qw, Bw = bitlen(Q), bitlen(B)
    V = layout.V
    assert len(data) == V
    p1, p2 = [], []
    fibers = 0

    def offset(pc):
        a, c = offset_fn(pc.val, layout)
        # reduce modulo Q = 2^b (low b bits) or general Q: charged O(A^2)
        aw = bitlen(abs(a)) + 1
        c += 2 * aw * (1 if Q & (Q - 1) == 0 else aw)
        cost.offset_calls += 1
        cost.offset_cost += c
        cost.max_offset_cost = max(cost.max_offset_cost, c)
        cost.fiber += c
        return a % Q

    # split pass
    pc = PrefixCounters(layout, cost)
    pos = 0
    while True:
        fibers += 1
        a = offset(pc)
        pos = copy_blocks(data, pos, p1, Q - a, B, Qw, Bw, cost)
        pos = copy_blocks(data, pos, p2, a, B, Qw, Bw, cost)
        if not pc.advance():
            break
    assert pos == V
    cost.data += pos + len(p1) + len(p2)       # rewind input and both pieces
    # merge pass
    out = []
    pc = PrefixCounters(layout, cost)
    i1 = i2 = 0
    while True:
        a = offset(pc)
        i2 = copy_blocks(p2, i2, out, a, B, Qw, Bw, cost)
        i1 = copy_blocks(p1, i1, out, Q - a, B, Qw, Bw, cost)
        if not pc.advance():
            break
    assert i1 == len(p1) and i2 == len(p2)
    cost.data += len(out) + len(p1) + len(p2)  # rewind output, clear pieces
    return out, cost, dict(fibers=fibers)


# ---------------------------------------------------------------- reference

def decode(idx, lengths):
    coords = []
    for L in reversed(lengths):
        coords.append(idx % L)
        idx //= L
    return coords[::-1]


def encode(coords, lengths):
    idx = 0
    for c, L in zip(coords, lengths):
        idx = idx * L + c
    return idx


def reference_rotation(layout, data, offset_value):
    """Direct definition: out[(.., (y + a(controls)) mod Q, ..)] = in[(.., y, ..)].
    offset_value(dict control index -> value) -> int."""
    V = layout.V
    out = [None] * V
    for idx in range(V):
        co = decode(idx, layout.lengths)
        a = offset_value({c: co[c] for c in layout.controls})
        co2 = list(co)
        co2[layout.ti] = (co[layout.ti] + a) % layout.Q
        out[encode(co2, layout.lengths)] = data[idx]
    return out
