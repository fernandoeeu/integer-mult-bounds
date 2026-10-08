"""Offset functions used by the compact-control construction
(notes/compact-control-movement.tex, 'Earlier source' / 'Later source'),
evaluated only through the control counters, with a bit-level charge.

Conventions (as in the text): n = f-1, j_i = rho + i*K, radix Bd = 2^G,
compact digit t_i = bits [iG, iG+G) of the compact field value (LSB digit 0).
Offsets are returned as integers (possibly negative or >= Q); the machine
reduces them mod Q and charges that reduction.
"""


def _bit(counter, j):
    return counter.read_bit(j)


def _digit(counter, i, G):
    v, c = 0, 0
    for k in range(G):
        b, cc = counter.read_bit(i * G + k)
        v |= b << k
        c += cc
    return v, c


def make(kind, idx, n, K, rho, G, W):
    """kind: first, second, load_y, unload, first_u, second_u, load_x.
    idx: dict role -> field index (controls). W: target width in bits,
    used to charge each shifted addition at 2*(W+G+2) moves."""
    addw = 2 * (W + G + 2)

    def fn(val, lay):
        cost = 0
        acc = 0
        for i in range(n):
            j = rho + i * K
            if kind in ("first", "second"):
                z, c = _bit(val[idx["x"]], j); cost += c
                ti, c = _digit(val[idx["t"]], i, G); cost += c
            elif kind in ("first_u", "second_u"):
                z, c = _bit(val[idx["u"]], i * G); cost += c   # u_i mod 2
                ti, c = _digit(val[idx["t"]], i, G); cost += c
            if kind in ("first", "first_u"):
                acc += 2 * z * ti * (1 << j); cost += 2 * addw
            elif kind in ("second", "second_u"):
                acc += z * (1 - 2 * ti) * (1 << j); cost += 2 * addw
            elif kind == "load_y":
                yb, c = _bit(val[idx["y"]], j); cost += c
                acc += yb << (i * G); cost += addw
            elif kind == "load_x":
                xb, c = _bit(val[idx["x"]], j); cost += c
                acc += xb << (i * G); cost += addw
            elif kind == "unload":
                yb, c = _bit(val[idx["y"]], j); cost += c
                xb, c = _bit(val[idx["x"]], j); cost += c
                acc -= (yb ^ xb) << (i * G); cost += addw
            else:
                raise ValueError(kind)
        return acc, cost + 2

    def ref(vals):
        acc = 0
        for i in range(n):
            j = rho + i * K
            if kind in ("first", "second"):
                z = (vals[idx["x"]] >> j) & 1
                ti = (vals[idx["t"]] >> (i * G)) & ((1 << G) - 1)
            elif kind in ("first_u", "second_u"):
                z = (vals[idx["u"]] >> (i * G)) & 1
                ti = (vals[idx["t"]] >> (i * G)) & ((1 << G) - 1)
            if kind in ("first", "first_u"):
                acc += 2 * z * ti * (1 << j)
            elif kind in ("second", "second_u"):
                acc += z * (1 - 2 * ti) * (1 << j)
            elif kind == "load_y":
                acc += ((vals[idx["y"]] >> j) & 1) << (i * G)
            elif kind == "load_x":
                acc += ((vals[idx["x"]] >> j) & 1) << (i * G)
            elif kind == "unload":
                acc -= (((vals[idx["y"]] >> j) ^ (vals[idx["x"]] >> j)) & 1) << (i * G)
        return acc

    return fn, ref


def table_offset(table, controls):
    """Arbitrary offset function given as a table over the tuple of control
    values. Charged as reading every control bit once plus 2 moves."""

    def fn(val, lay):
        cost = 2
        key = []
        for c in controls:
            ctr = val[c]
            v = 0
            for j in range(ctr.width):
                b, cc = ctr.read_bit(j)
                v |= b << j
                cost += 2
            key.append(v)
        return table(tuple(key)), cost

    def ref(vals):
        return table(tuple(vals[c] for c in controls))

    return fn, ref
