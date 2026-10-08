"""Explicit record-level simulation of the recursive layout on tiny instances.

Every record address is materialized.  The layer is executed with toy
operators that obey the layout contract:
  * individual kernels: a random invertible 2x2 matrix M_i (mod a prime) on
    the selected bit rho of chunk i (stands in for C);
  * compact operations: a random dirty bijection of the carved u,t,b fields
    driven by the slot bits, then its inverse (stands in for the swap /
    rotation sequence, which must restore the temporaries);
  * the network: a random invertible W x W matrix A mixing aligned records of
    the W role streams, the recursive child calls on every role stream for
    every slot, then A^{-1};
  * leaves: individual kernels on the leaf's chunks.
The true layer is the tensor product of all M_i applied to the unpadded
array; it is computed independently and compared.  At every node the
explicit address sets are checked: complete within-row ranges in every role,
exactly 1/W of the parent volume, aligned role streams, padding as whole rows,
exact reassembly, and removal of the padded rows (which become nonzero in the
middle of the computation, so no zero-scratch assumption is used).

Row / reserved chunk counts can be given as written (from m, W, d, G, K) or
overridden by small values so that the address space stays enumerable; the
override is reported.
"""
import random, itertools, sys, zlib
from fractions import Fraction as F
from layout_sim import ceil_log, cdiv, lt_power

PR = 1_000_003


def inv_mod(a):
    return pow(a, PR - 2, PR)


def rand_inv2(rng):
    while True:
        a, b, c, d = (rng.randrange(PR) for _ in range(4))
        if (a * d - b * c) % PR:
            return (a, b, c, d)


def rand_invW(W, rng):
    while True:
        A = [[rng.randrange(PR) for _ in range(W)] for _ in range(W)]
        Ainv = mat_inv(A)
        if Ainv is not None:
            return A, Ainv


def mat_inv(A):
    n = len(A)
    M = [row[:] + [int(i == j) for j in range(n)] for i, row in enumerate(A)]
    for col in range(n):
        piv = next((r for r in range(col, n) if M[r][col] % PR), None)
        if piv is None:
            return None
        M[col], M[piv] = M[piv], M[col]
        iv = inv_mod(M[col][col])
        M[col] = [x * iv % PR for x in M[col]]
        for r in range(n):
            if r != col and M[r][col]:
                fct = M[r][col]
                M[r] = [(x - fct * y) % PR for x, y in zip(M[r], M[col])]
    return [row[n:] for row in M]


class Fail(Exception):
    pass


def need(cond, msg):
    if not cond:
        raise Fail(msg)


class Explicit:
    def __init__(self, m, W, d, D, K, G, beta, P=1, S=1, rho=0, q0=None, qF=None, qB=None, H=None,
                 k0=None, pad_mode="ceil", front_rem="after", carve_at="low", seed=0):
        self.m, self.W, self.d, self.D, self.K, self.G, self.beta = m, W, d, D, K, G, beta
        self.P, self.S, self.rho = P, S, rho
        self.H = d * G if H is None else H
        self.qF = cdiv(2 * self.H, K) if qF is None else qF
        self.qB = cdiv(self.H, K) if qB is None else qB
        self.q0 = ceil_log(2, W) * ceil_log(m, 2 * d) if q0 is None else q0
        self.k0 = ceil_log(m, d) if k0 is None else k0
        self.Q0 = self.q0 + self.qF + self.qB
        self.pad_mode, self.front_rem, self.carve_at = pad_mode, front_rem, carve_at
        self.rng = random.Random(seed)
        self.Ms = [rand_inv2(self.rng) for _ in range(D)]
        self.stats = dict(nodes=0, internal=0, leaves=0, compact=0, padded_nonzero_midway=False,
                          max_depth=0, role_checks=0)
        need(self.qF * K >= 2 * self.H and self.qB * K >= self.H, "reserved chunks too short")
        need(2 ** (self.q0 * K) >= W ** self.k0, "R_row < W^k0 (override inconsistent)")

    # ----- address helpers: within-row part = tuple of chunks q0..D-1
    def chunkbit(self, ch, i):
        """selected bit of chunk value ch (bit rho numbered from LSB)."""
        return (ch >> self.rho) & 1

    def apply_kernel(self, stream, key_chunk_index):
        """Apply M_i on the selected bit of chunk i (index into the within-row
        tuple, i.e. global chunk q0 + idx) for a dict stream keyed by
        (prefix, g, rest_tuple, s).  Needs the complete selected-bit range."""
        i = key_chunk_index
        a, b, c, d = self.Ms[self.q0 + i]
        out = {}
        for key, v in stream.items():
            pfx, g, rest, s = key
            bit = (rest[i] >> self.rho) & 1
            if bit:
                continue
            r1 = list(rest); r1[i] |= (1 << self.rho)
            k1 = (pfx, g, tuple(r1), s)
            need(k1 in stream, "selected bit lacks complete range")
            v0, v1 = v, stream[k1]
            out[key] = (a * v0 + b * v1) % PR
            out[k1] = (c * v0 + d * v1) % PR
        need(len(out) == len(stream), "kernel lost records")
        return out

    # ----- bit-level carving within the row (bits of chunks q0..D-1)
    def carved_positions(self, n):
        K, H, G = self.K, self.H, self.G
        base = self.q0 * K
        flen = self.qF * K
        rem = flen - 2 * H
        if self.front_rem == "after":
            h1, h2 = base, base + H
        else:
            h1, h2 = base + rem, base + rem + H
        b0 = (self.D - self.qB) * K
        brem = self.qB * K - H
        hb = b0 if self.front_rem == "after" else b0 + brem
        w = n * G
        off = {"low": 0, "high": H - w, "mid": (H - w) // 2}[self.carve_at]
        return [list(range(h + off, h + off + w)) for h in (h1, h2, hb)]

    def get_bits(self, rest, positions):
        """read global bit positions (MSB-first numbering) from rest tuple."""
        K = self.K
        out = 0
        for p in positions:
            ci = p // K - self.q0
            bi = K - 1 - (p % K)
            out = (out << 1) | ((rest[ci] >> bi) & 1)
        return out

    def set_bits(self, rest, positions, val):
        K = self.K
        r = list(rest)
        for j, p in enumerate(reversed(positions)):
            ci = p // K - self.q0
            bi = K - 1 - (p % K)
            bit = (val >> j) & 1
            r[ci] = (r[ci] & ~(1 << bi)) | (bit << bi)
        return tuple(r)

    def compact_dirty(self, stream, piece_start, e, n):
        """A dirty bijection on the carved u,t,b fields controlled by the
        slot bits (data independent), followed by its inverse.  Checks that
        each record stays in its row with the same non-carved coordinates,
        and that the address set of every row is preserved."""
        pu, pt, pb = self.carved_positions(n)
        K = self.K
        a0, a1 = piece_start * K, (piece_start + e) * K
        need(max(pu + pt) < a0 and min(pb) >= a1, "carved fields not before/after slots")
        need(not set(pu) & set(pt), "u,t overlap")
        need(min(pu + pt + pb) >= self.q0 * K, "carved field in row index")
        slot_pos = list(range(a0, a1))
        w = n * self.G
        mod = 1 << w
        salt = self.rng.randrange(1 << 30)

        def fwd(rest, sign):
            ctrl = self.get_bits(rest, slot_pos)
            hsh = hash((ctrl, salt)) % mod
            u = self.get_bits(rest, pu); t = self.get_bits(rest, pt); b = self.get_bits(rest, pb)
            if sign > 0:
                t = (t + hsh + u) % mod; b = (b ^ t); u = (u + 2 * hsh + 1) % mod
            else:
                u = (u - 2 * hsh - 1) % mod; b = (b ^ t); t = (t - hsh - u) % mod
            rest = self.set_bits(rest, pu, u); rest = self.set_bits(rest, pt, t)
            return self.set_bits(rest, pb, b)

        moved = {}
        for (pfx, g, rest, s), v in stream.items():
            moved[(pfx, g, fwd(rest, +1), s)] = v
        need(len(moved) == len(stream), "dirty op not a bijection")
        need(set(moved) == set(stream), "dirty op changed the address set")
        back = {}
        for (pfx, g, rest, s), v in moved.items():
            back[(pfx, g, fwd(rest, -1), s)] = v
        need(back == stream, "dirty op not restored")
        return back

    def node(self, stream, piece_start, e, depth, rows):
        """stream keyed (prefix, g, rest, s) with g in [0, rows) for each prefix."""
        st = self.stats
        st["nodes"] += 1
        st["max_depth"] = max(st["max_depth"], depth)
        need(depth <= self.k0, "depth exceeds k0")
        within = self.within_set
        keys = set(stream)
        need(len(stream) == self.P * rows * len(within) * self.S, "node volume")
        if lt_power(e, self.d, self.beta):
            st["leaves"] += 1
            for i in range(piece_start, piece_start + e):
                stream = self.apply_kernel(stream, i - self.q0)
            return stream
        st["internal"] += 1
        m, W = self.m, self.W
        need(e % m == 0 and e >= m, "internal node cannot form m slots")
        f = e // m
        n = f - 1
        if n >= 1:
            need(n * self.G <= self.H, "nG > H")
            st["compact"] += 1
            stream = self.compact_dirty(stream, piece_start, e, n)
        need(rows % W == 0, f"rows {rows} not divisible by W")
        cr = rows // W
        roles = [dict() for _ in range(W)]
        for (pfx, g, rest, s), v in stream.items():
            roles[g % W][(pfx, g // W, rest, s)] = v
        expect_keys = None
        for r in roles:
            ks = set(r)
            need(len(r) * W == len(stream), "child volume not exactly 1/W")
            if expect_keys is None:
                expect_keys = ks
                need(ks == {(p, g, x, s) for p in range(self.P) for g in range(cr)
                            for x in within for s in range(self.S)}, "role lacks complete within-row set")
            need(ks == expect_keys, "role streams not aligned")
            st["role_checks"] += 1
        A, Ainv = rand_invW(W, self.rng)

        def mix(roles, M):
            new = [dict() for _ in range(W)]
            for k in expect_keys:
                vec = [r[k] for r in roles]
                for i in range(W):
                    new[i][k] = sum(M[i][j] * vec[j] for j in range(W)) % PR
            return new
        roles = mix(roles, A)
        # padded rows are now mixed with genuine ones
        for w in range(W):
            for (pfx, g, rest, s), v in roles[w].items():
                if self.depth_row_is_padded(rows, g * W + w, depth) and v:
                    st["padded_nonzero_midway"] = True
                    break
        for h in range(m):
            for w in range(W):
                self._path.append(w)
                roles[w] = self.node(roles[w], piece_start + h * f, f, depth + 1, cr)
                self._path.pop()
        roles = mix(roles, Ainv)
        out = {}
        for w in range(W):
            for (pfx, g, rest, s), v in roles[w].items():
                out[(pfx, g * W + w, rest, s)] = v
        need(set(out) == keys, "reassembly changed address set")
        return out

    def depth_row_is_padded(self, rows, g_local, depth):
        # reconstruct original padded row index from the role path
        u = g_local
        for w in reversed(self._path):
            u = u * self.W + w
        return u >= self.R_row

    def run(self):
        K, D, P, S = self.K, self.D, self.P, self.S
        rng = self.rng
        # original array
        orig = {}
        for pfx in range(P):
            for chunks in itertools.product(range(1 << K), repeat=D):
                for s in range(S):
                    orig[(pfx, chunks, s)] = rng.randrange(PR)
        # independent expected result: all D kernels
        exp = dict(orig)
        for i in range(D):
            a, b, c, d = self.Ms[i]
            new = {}
            for (pfx, ch, s), v in exp.items():
                if (ch[i] >> self.rho) & 1:
                    continue
                c1 = list(ch); c1[i] |= 1 << self.rho; c1 = tuple(c1)
                v1 = exp[(pfx, c1, s)]
                new[(pfx, ch, s)] = (a * v + b * v1) % PR
                new[(pfx, c1, s)] = (c * v + d * v1) % PR
            exp = new
        if D <= self.Q0:
            self.stats["mode"] = "fallback"
            res = dict(orig)
            # individual kernels on all D axes, via the same routine
            st = {(pfx, 0, ch, s): v for (pfx, ch, s), v in res.items()}
            sv_q0 = self.q0
            self.q0 = 0
            for i in range(D):
                st = self.apply_kernel(st, i)
            self.q0 = sv_q0
            res = {(pfx, ch, s): v for (pfx, _, ch, s), v in st.items()}
            need(res == exp, "fallback result differs")
            return self.stats
        self.stats["mode"] = "recursive"
        q0 = self.q0
        # row index u from chunks 0..q0-1 (big-endian)
        def u_of(ch):
            u = 0
            for x in ch[:q0]:
                u = (u << K) | x
            return u
        def ch_of(u):
            out = []
            for _ in range(q0):
                out.append(u & ((1 << K) - 1)); u >>= K
            return tuple(reversed(out))
        stream = {(pfx, u_of(ch), ch[q0:], s): v for (pfx, ch, s), v in orig.items()}
        self.within_set = sorted({k[2] for k in stream})
        need(len(self.within_set) == 2 ** (K * (D - q0)), "within-row set incomplete at root")
        # individual kernels on the first q0+qF and last qB chunks
        R_row = 1 << (q0 * K)
        self.R_row = R_row
        # row-index chunks: operate on u directly through a temporary view
        full = {(pfx, 0, ch_of(u) + rest, s): v for (pfx, u, rest, s), v in stream.items()}
        sv = self.q0; self.q0 = 0
        for i in list(range(sv + self.qF)) + list(range(D - self.qB, D)):
            full = self.apply_kernel(full, i)
        self.q0 = sv
        stream = {(pfx, u_of(ch), ch[q0:], s): v for (pfx, _, ch, s), v in full.items()}
        # padding
        Wk = self.W ** self.k0
        if self.pad_mode == "ceil":
            Rp = cdiv(R_row, Wk) * Wk
        else:
            Rp = (R_row // Wk + 1) * Wk
        need(Rp <= 2 * R_row, "padding more than doubles")
        for pfx in range(P):
            for u in range(R_row, Rp):
                for x in self.within_set:
                    for s in range(S):
                        stream[(pfx, u, x, s)] = 0
        self.stats["pad_rows"] = Rp - R_row
        self.stats["R_row"] = R_row
        self.stats["Rp"] = Rp
        # pieces
        L = D - self.Q0
        digs = []
        while L:
            digs.append(L % self.m); L //= self.m
        pieces = []
        for j, a in enumerate(digs):
            pieces += [self.m ** j] * a
        pieces.reverse()
        start = q0 + self.qF
        self._path = []
        for e in pieces:
            stream = self.node(stream, start, e, 0, Rp)
            start += e
        need(start == D - self.qB, "pieces do not end at back block")
        # padded rows must be zero; delete them
        for (pfx, u, x, s), v in stream.items():
            if u >= R_row:
                need(v == 0, "padded row nonzero at completion")
        res = {(pfx, ch_of(u) + x, s): v for (pfx, u, x, s), v in stream.items() if u < R_row}
        need(res == exp, "final result differs from the tensor-product layer")
        return self.stats


CONFIGS = [
    # (m, W, d, D, K, G, beta, P, S, rho, overrides)
    # as-written q0/k0 with small free G/H overrides so that the space is enumerable
    dict(m=2, W=3, d=8, D=7, K=2, G=1, beta=F(1, 2), P=1, S=1, rho=0, q0=2, qF=1, qB=1, H=1, k0=2),
    dict(m=2, W=3, d=8, D=7, K=2, G=1, beta=F(1, 2), P=2, S=2, rho=1, q0=2, qF=1, qB=1, H=1, k0=2),
    dict(m=2, W=3, d=8, D=8, K=2, G=1, beta=F(1, 1000), P=1, S=1, rho=1, q0=2, qF=1, qB=1, H=1, k0=2),
    dict(m=2, W=2, d=8, D=7, K=2, G=1, beta=F(1, 1000), P=1, S=2, rho=0, q0=1, qF=1, qB=1, H=1, k0=2),
    dict(m=2, W=5, d=8, D=7, K=2, G=1, beta=F(1, 1000), P=1, S=1, rho=0, q0=3, qF=1, qB=1, H=1, k0=2),
    dict(m=2, W=4, d=8, D=7, K=2, G=1, beta=F(1, 1000), P=1, S=1, rho=1, q0=2, qF=1, qB=1, H=1, k0=2),
    dict(m=3, W=3, d=9, D=6, K=2, G=1, beta=F(1, 1000), P=2, S=1, rho=0, q0=2, qF=1, qB=1, H=1, k0=2),
    dict(m=2, W=3, d=4, D=6, K=1, G=1, beta=F(1, 1000), P=1, S=1, rho=0, q0=2, qF=2, qB=1, H=1, k0=1),
    dict(m=2, W=5, d=8, D=8, K=2, G=1, beta=F(1, 1000), P=1, S=1, rho=1, q0=3, qF=1, qB=1, H=1, k0=2),
    dict(m=2, W=4, d=8, D=8, K=2, G=1, beta=F(1, 1000), P=1, S=1, rho=0, q0=2, qF=1, qB=1, H=1, k0=2),
    dict(m=2, W=3, d=8, D=8, K=2, G=1, beta=F(1, 1000), P=2, S=1, rho=0, q0=2, qF=1, qB=1, H=1, k0=2, pad_mode="strict"),
    # strict / before / high / mid readings
    dict(m=2, W=3, d=8, D=7, K=2, G=1, beta=F(1, 1000), P=1, S=1, rho=0, q0=2, qF=1, qB=1, H=1, k0=2, pad_mode="strict"),
    dict(m=2, W=3, d=8, D=8, K=2, G=1, beta=F(1, 1000), P=1, S=1, rho=1, q0=2, qF=2, qB=1, H=2, k0=2, front_rem="before", carve_at="high"),
    dict(m=2, W=3, d=8, D=8, K=2, G=1, beta=F(1, 1000), P=1, S=1, rho=1, q0=2, qF=2, qB=2, H=2, k0=2, front_rem="after", carve_at="mid"),
    # fallback threshold
    dict(m=2, W=3, d=8, D=4, K=2, G=1, beta=F(1, 1000), P=1, S=1, rho=0, q0=2, qF=1, qB=1, H=1, k0=2),
    dict(m=2, W=3, d=8, D=5, K=2, G=1, beta=F(1, 1000), P=1, S=1, rho=0, q0=2, qF=1, qB=1, H=1, k0=2),
    # fully as written (no overrides, G=1 free): necessarily the small-D fallback,
    # since recursion as written needs D > Q0 >= 3dG/K + log terms, i.e. an
    # address space far beyond enumeration.
    dict(m=2, W=2, d=2, D=2, K=2, G=1, beta=F(1, 1000), P=2, S=2, rho=1),
    dict(m=3, W=2, d=3, D=3, K=2, G=1, beta=F(1, 1000), P=1, S=1, rho=0),
]


def main():
    allok = True
    for cfg in CONFIGS:
        cfg = dict(cfg)
        seed = zlib.crc32(repr(sorted(cfg.items())).encode())
        try:
            ex = Explicit(seed=seed, **cfg)
            st = ex.run()
            print("OK  ", {k: v for k, v in cfg.items()}, "->", st)
        except Fail as e:
            allok = False
            print("FAIL", cfg, e)
    print("explicit simulation:", "all invariants hold" if allok else "FAILURES")


if __name__ == "__main__":
    main()
