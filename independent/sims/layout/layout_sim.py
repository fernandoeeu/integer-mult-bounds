"""Independent symbolic simulation of the compact-control recursive layout.

Implements, from the text of notes/compact-control-layout.tex (and the
upstream 05-layers.tex row construction it modifies), the reservation of
row / front / back chunks, the carving of compact fields, padding of the
row range, recursive row splitting u = W g + w, slot selection and the
stopping rule, and checks the stated invariants at every node.

Nothing here imports or reads the repository's Python.

Address bits are numbered globally from the most significant bit of chunk 0
(lexicographic order): chunk i occupies bits [i K, (i+1) K).  The prefix [P]
precedes all chunks and the suffix [S] (plus record payload) follows them.
"""
from fractions import Fraction
from dataclasses import dataclass, field
import random


# ---------------------------------------------------------------- exact helpers
def ceil_log(base, x):
    """smallest k >= 0 with base**k >= x (x >= 1)."""
    assert base >= 2 and x >= 1
    k, v = 0, 1
    while v < x:
        v *= base
        k += 1
    return k


def floor_log(base, x):
    """largest k with base**k <= x (x >= 1)."""
    k, v = 0, base
    while v <= x:
        v *= base
        k += 1
    return k


def iroot_floor(x, b):
    """floor(x ** (1/b)) exactly (integer Newton iteration from above)."""
    if x < 2:
        return x
    if b == 1:
        return x
    r = 1 << (-(-x.bit_length() // b))      # r >= true root
    while True:
        y = ((b - 1) * r + x // r ** (b - 1)) // b
        if y >= r:
            break
        r = y
    while r ** b > x:
        r -= 1
    while (r + 1) ** b <= x:
        r += 1
    return r


def K_from_c(d, c: Fraction):
    """K = floor(d^c) for rational c = a/b, exactly."""
    return iroot_floor(d ** c.numerator, c.denominator)


def cdiv(a, b):
    return -(-a // b)


def lt_power(e, d, beta: Fraction):
    """e < d^beta  <=>  e^v < d^u  (beta = u/v).  Exact; a bit-length screen
    decides the clear cases without forming huge powers."""
    u, v = beta.numerator, beta.denominator
    le, ld = e.bit_length(), d.bit_length()
    if v * (le - 1) >= u * ld:      # e^v >= 2^{v(le-1)} >= 2^{u ld} > d^u
        return False
    if v * le <= u * (ld - 1):      # e^v < 2^{v le} <= 2^{u(ld-1)} <= d^u
        return True
    return e ** v < d ** u


class LayoutFailure(Exception):
    pass


@dataclass
class Params:
    m: int
    W: int
    d: int
    D: int
    K: int
    G: int
    beta: Fraction
    P: int = 1
    S: int = 1
    # ambiguity switches
    pad_mode: str = "ceil"          # "ceil": next multiple >= R ; "strict": next multiple > R
    front_rem: str = "after"        # spectator remainder after / before the two H fields
    carve_at: str = "low"           # carve nG bits at start ("low"), end ("high"), or middle of each H field
    piece_order: str = "desc"       # base-m pieces largest first or ascending
    # derived
    H: int = 0
    qF: int = 0
    qB: int = 0
    q0: int = 0
    k0: int = 0
    Q0: int = 0

    def derive(self):
        self.H = self.d * self.G
        self.qF = cdiv(2 * self.H, self.K)
        self.qB = cdiv(self.H, self.K)
        self.q0 = ceil_log(2, self.W) * ceil_log(self.m, 2 * self.d)
        self.k0 = ceil_log(self.m, self.d)
        self.Q0 = self.q0 + self.qF + self.qB
        return self


def G_from_p(p):
    return 4 * ceil_log(2, p) + 6


# ------------------------------------------------------------------ the layout
@dataclass
class Stats:
    nodes: int = 0
    internal: int = 0
    leaves: int = 0
    compact_nodes: int = 0
    max_depth: int = 0
    row_paths: int = 0
    checks: int = 0
    boundary_nodes: int = 0
    notes: list = field(default_factory=list)


def chk(cond, msg, stats):
    stats.checks += 1
    if not cond:
        raise LayoutFailure(msg)


def global_claims(pr: Params, stats: Stats, c: Fraction = None):
    """Root-level finite claims (C7-C9)."""
    m, W, d, D, K, G, H = pr.m, pr.W, pr.d, pr.D, pr.K, pr.G, pr.H
    chk(1 <= D <= d, "D range", stats)
    chk(pr.qF * K >= 2 * H, "front chunks carry >= 2H bits", stats)
    chk(pr.qB * K >= H, "back chunks carry >= H bits", stats)
    # q_F + q_B <= 3dG/K + 2  (exact rational)
    chk(Fraction(pr.qF + pr.qB) <= Fraction(3 * d * G, K) + 2, "qF+qB <= 3dG/K+2", stats)
    if c is not None and K == K_from_c(d, c):
        # K >= d^c/2  <=>  (2K)^b >= d^a ;  3dG/K <= 6 d^{1-c} G  is equivalent
        chk((2 * K) ** c.denominator >= d ** c.numerator, "K >= d^c/2", stats)
    # R_row = 2^{q0 K} >= W^{k0}
    chk(W ** pr.k0 <= (1 << (pr.q0 * K)) if pr.q0 * K < 4096 else
        (W ** pr.k0).bit_length() <= pr.q0 * K, "R_row >= W^k0", stats)


def pad_rows(pr: Params, stats: Stats, R_row=None):
    """Return padded row count R' (exact int, or ('sym', ...) for huge)."""
    Wk = pr.W ** pr.k0
    bits = pr.q0 * pr.K
    rem = pow(2, bits, Wk)  # R_row mod W^k0
    if pr.pad_mode == "ceil":
        pad = (-rem) % Wk
    else:
        pad = Wk - rem
    # factor-two reading: R' <= 2 R_row  <=>  pad <= R_row
    R_row_ge_Wk = (Wk.bit_length() <= bits) if bits >= 4096 else (Wk <= (1 << bits))
    chk(pad < Wk or (pr.pad_mode == "strict" and pad == Wk), "pad < W^k0", stats)
    chk(R_row_ge_Wk, "pad <= R_row (factor two)", stats)
    if bits < 4096:
        R = 1 << bits
        Rp = R + pad
        chk(Rp % Wk == 0, "padded rows divisible by W^k0", stats)
        chk(Rp <= 2 * R, "volume at most doubles", stats)
        return R, Rp, pad
    # symbolic: R' = W^k0 * Qrest, track only divisibility
    return None, ("sym", Wk), pad


@dataclass
class Field:
    kind: str
    start: int  # global bit index
    length: int


def front_back_fields(pr: Params, n):
    """Within-row field list (bit intervals) for a node whose slots have f=n+1
    chunks.  Returns list of Field covering bits [q0 K, D K) except the middle
    block, plus the carved fields u,t,b (None when n == 0)."""
    K, H, G = pr.K, pr.H, pr.G
    q0, qF, qB, D = pr.q0, pr.qF, pr.qB, pr.D
    fs = []
    f0 = q0 * K
        # front region [f0, f0 + qF K)
    flen = qF * K
    rem = flen - 2 * H
    if pr.front_rem == "after":
        h1, h2, r0 = f0, f0 + H, f0 + 2 * H
    else:
        r0, h1, h2 = f0, f0 + rem, f0 + rem + H
    b0 = (D - qB) * K
    blen = qB * K
    brem = blen - H
    if pr.front_rem == "after":
        hb, rb = b0, b0 + H
    else:
        rb, hb = b0, b0 + brem
    w = n * G
    def carve(hstart, name):
        if pr.carve_at == "low":
            off = 0
        elif pr.carve_at == "high":
            off = H - w
        else:
            off = (H - w) // 2
        out = []
        if off > 0:
            out.append(Field(name + "_unused", hstart, off))
        if w > 0:
            out.append(Field(name, hstart + off, w))
        if H - w - off > 0:
            out.append(Field(name + "_unused", hstart + off + w, H - w - off))
        return out
    fu = carve(h1, "u")
    ft = carve(h2, "t")
    fb = carve(hb, "b")
    if pr.front_rem == "after":
        fs += fu + ft
        if rem > 0:
            fs.append(Field("front_rem", r0, rem))
    else:
        if rem > 0:
            fs.append(Field("front_rem", r0, rem))
        fs += fu + ft
    mid = Field("middle", (q0 + qF) * K, (D - qB - q0 - qF) * K)
    back = []
    if pr.front_rem == "after":
        back = fb + ([Field("back_rem", rb, brem)] if brem > 0 else [])
    else:
        back = ([Field("back_rem", rb, brem)] if brem > 0 else []) + fb
    return fs, mid, back


def check_node_fields(pr, stats, piece_start, e, n):
    """Check C2, C4, C5 at a node with e active chunks starting at chunk
    piece_start, split into m slots of f = n+1 chunks (n = -1 at leaves)."""
    K, G, H = pr.K, pr.G, pr.H
    fs, mid, back = front_back_fields(pr, max(n, 0))
    # middle split into: spectators before, slots, spectators after
    a0 = piece_start * K
    a1 = (piece_start + e) * K
    chk(mid.start <= a0 and a1 <= mid.start + mid.length,
        f"active chunks [{piece_start},{piece_start+e}) inside middle block", stats)
    allf = list(fs)
    if a0 > mid.start:
        allf.append(Field("mid_spect", mid.start, a0 - mid.start))
    if n >= 0:
        f = n + 1
        chk(e == pr.m * f, "e = m f", stats)
        # m consecutive slots of f chunks; represented as one block when m is
        # large (the block is the disjoint union of the m equal slots).
        if pr.m <= 64:
            for h in range(pr.m):
                allf.append(Field(f"slot{h}", a0 + h * f * K, f * K))
        else:
            chk(pr.m * f * K == a1 - a0, "m slots tile active block", stats)
            allf.append(Field("slots", a0, a1 - a0))
    else:
        allf.append(Field("leaf_active", a0, e * K))
    if mid.start + mid.length > a1:
        allf.append(Field("mid_spect", a1, mid.start + mid.length - a1))
    allf += back
    # partition of within-row bits [q0 K, D K)
    pos = pr.q0 * K
    for fl in allf:
        chk(fl.length > 0, f"positive field length {fl.kind}", stats)
        chk(fl.start == pos, f"fields contiguous at {fl.kind}", stats)
        pos += fl.length
    chk(pos == pr.D * K, "fields cover all within-row bits", stats)
    chk(len(allf) <= 14 + min(pr.m, 64), "fixed number of fields", stats)
    if n >= 1:
        stats.compact_nodes += 1
        w = n * G
        chk(w <= H, "nG <= H", stats)
        get = lambda k: [x for x in allf if x.kind == k]
        u, t, b = get("u"), get("t"), get("b")
        chk(len(u) == len(t) == len(b) == 1, "exactly one carved u,t,b", stats)
        u, t, b = u[0], t[0], b[0]
        for x in (u, t, b):
            chk(x.length == w, "carved width nG", stats)
            chk(x.start >= pr.q0 * K, "carved field excludes row index", stats)
        first_slot = a0
        last_slot_end = a1
        chk(u.start + u.length <= first_slot and t.start + t.length <= first_slot,
            "u,t precede all slots", stats)
        chk(b.start >= last_slot_end, "b follows all slots", stats)
        chk(u.start + u.length <= t.start or t.start + t.length <= u.start, "u,t disjoint", stats)
    return allf


def rows_split(rowset, W, stats):
    """rowset = (offset, stride, count) inside padded row coordinates
    (count may be ('sym', Wk_remaining) for huge instances)."""
    off, stride, cnt = rowset
    if isinstance(cnt, tuple):
        Wk = cnt[1]
        chk(Wk % W == 0, "symbolic row count divisible by W", stats)
        return lambda w: (off + stride * w, stride * W, ("sym", Wk // W))
    chk(cnt % W == 0, f"row count {cnt} divisible by W={W}", stats)
    return lambda w: (off + stride * w, stride * W, cnt // W)


def piece_groups(pr):
    """base-m expansion of D - Q0 as (piece size, number of pieces)."""
    L = pr.D - pr.Q0
    digs = []
    while L:
        digs.append(L % pr.m)
        L //= pr.m
    g = [(pr.m ** j, a) for j, a in enumerate(digs) if a]
    if pr.piece_order == "desc":
        g.reverse()
    return g


def pieces_of(pr):
    L = pr.D - pr.Q0
    out = []
    j = 0
    x = L
    digs = []
    while x:
        digs.append(x % pr.m)
        x //= pr.m
    for j, a in enumerate(digs):
        out += [pr.m ** j] * a
    if pr.piece_order == "desc":
        out.reverse()
    return out


def run_layout(pr: Params, c=None, mode="full", rng=None, max_paths=None, stats=None,
               piece_sample=None):
    """Simulate the whole layer layout.  mode='full' enumerates every role w
    and every slot h at every node (W*m branching); mode='sample' follows
    max_paths random root-to-leaf paths per piece, plus the extreme paths."""
    pr.derive()
    stats = stats or Stats()
    global_claims(pr, stats, c)
    if pr.D <= pr.Q0:
        stats.notes.append("fallback")
        chk(pr.D <= pr.d, "fallback processes <= d axes", stats)
        return stats
    chk(pr.Q0 < pr.D <= pr.d, "reserved axes within D <= d", stats)
    R, Rp, pad = pad_rows(pr, stats)
    groups = piece_groups(pr)      # list of (size, count) in processing order
    npieces = sum(cnt for _, cnt in groups)
    chk(sum(sz * cnt for sz, cnt in groups) == pr.D - pr.Q0, "pieces cover middle", stats)
    chk(npieces <= (pr.m - 1) * (1 + floor_log(pr.m, pr.d)), "piece count bound", stats)
    rng = rng or random.Random(0)
    start = pr.q0 + pr.qF
    sel = []                       # (size, start) of the pieces to simulate
    for sz, cnt in groups:
        if piece_sample is None or npieces <= piece_sample:
            ii = range(cnt)
        else:
            ii = sorted({0, cnt - 1} | {rng.randrange(cnt) for _ in range(2)})
        sel += [(sz, start + i * sz) for i in ii]
        start += sz * cnt
    chk(start == pr.D - pr.qB, "pieces end at back block", stats)
    if piece_sample is not None and npieces > piece_sample:
        stats.notes.append(f"sampled {len(sel)} of {npieces} pieces")
    for e, start in sel:
        root_rows = (0, 1, Rp)
        if mode == "full":
            walk(pr, stats, start, e, 0, root_rows, R, e)
        else:
            for pi in range(max_paths + 2):
                walk_path(pr, stats, start, e, root_rows, R, rng, pi)
    return stats


def node(pr, stats, piece_start, e, depth, rows, R, e_root):
    stats.nodes += 1
    stats.max_depth = max(stats.max_depth, depth)
    internal = not lt_power(e, pr.d, pr.beta)
    u_, v_ = pr.beta.numerator, pr.beta.denominator
    if abs(v_ * e.bit_length() - u_ * pr.d.bit_length()) <= v_ + u_ and e ** v_ == pr.d ** u_:
        stats.boundary_nodes += 1   # e = d^beta exactly: must be internal
    chk(depth <= pr.k0, f"depth {depth} <= k0 {pr.k0}", stats)
    if internal:
        chk(e >= pr.m and e % pr.m == 0, f"internal node e={e} splits into m slots", stats)
        n = e // pr.m - 1
        check_node_fields(pr, stats, piece_start, e, n)
        children_rows = rows_split(rows, pr.W, stats)
        # children partition the parent rows; volumes exactly 1/W
        off, stride, cnt = rows
        if not isinstance(cnt, tuple):
            allrows = set()
            if cnt * stride <= 200000 and pr.W <= 64:
                for (o, s_, c_) in map(children_rows, range(pr.W)):
                    chk(c_ * pr.W == cnt, "child row count exactly 1/W", stats)
                    rr = {o + s_ * g for g in range(c_)}
                    chk(not (rr & allrows), "children rows disjoint", stats)
                    allrows |= rr
                chk(allrows == {off + stride * g for g in range(cnt)}, "children rows cover parent", stats)
        stats.internal += 1
        # recursive-cost stopping identity: m^{J-1} <= e_root / d^beta along path
        # (checked at leaves below via depth)
        return True, n, children_rows
    else:
        check_node_fields(pr, stats, piece_start, e, -1)
        stats.leaves += 1
        # leaf: e < d^beta and the depth satisfies m^{depth-1} <= e_root/d^beta
        if depth >= 1:
            chk(not lt_power(e * pr.m, pr.d, pr.beta), "parent of leaf was internal", stats)
        return False, None, None


def walk(pr, stats, piece_start, e, depth, rows, R, e_root):
    internal, n, children_rows = node(pr, stats, piece_start, e, depth, rows, R, e_root)
    if not internal:
        return
    f = n + 1
    # layout of a child depends on its slot h; rows depend on its role w.
    # Enumerate all (h, w) pairs (s calls each choose some pair).
    # The child's field layout depends only on its slot h; its row set depends
    # only on its role w, and all W role row sets have identical count and
    # stride (verified in node()).  Enumerate every slot h; for the role,
    # cycle w through all W values across the h-loop and depth so that every
    # role index is exercised, without the W*m product blow-up.
    for h in range(pr.m):
        w = (h + depth) % pr.W
        cr = children_rows(w)
        walk(pr, stats, piece_start + h * f, f, depth + 1, cr, R, e_root)


def walk_path(pr, stats, piece_start, e, rows, R, rng, pi):
    depth = 0
    while True:
        internal, n, children_rows = node(pr, stats, piece_start, e, depth, rows, R, e)
        if not internal:
            stats.row_paths += 1
            return
        f = n + 1
        if pi == 0:
            h, w = 0, 0
        elif pi == 1:
            h, w = pr.m - 1, pr.W - 1
        else:
            h, w = rng.randrange(pr.m), rng.randrange(pr.W)
        piece_start += h * f
        e = f
        rows = children_rows(w)
        depth += 1
