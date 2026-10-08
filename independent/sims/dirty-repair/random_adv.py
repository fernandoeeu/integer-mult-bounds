"""Randomised and adversarial tests at the proposition's parameters
(G = 4*ceil(log2 p) + 6, f <= p, K at and above the cutoff K >= G + 4 l_p + 10)
and at small/irregular K, with arbitrary-precision addresses.

For each address q:
  * S(q) == T(q) when q is good; S^{-1}(S q) == q; bad(S q) == bad(q);
  * repaired + highest XOR == full selected-bit addition, u,t,b,x restored;
  * stepwise: on good q, after every rotation the K-bit segments of y and
    the G-bit digits of the temporaries equal an unbounded-integer model of
    the four-update identity (no carry/borrow between segments or digits),
    and the maximal |g displacement| is recorded against the claimed 2B.
"""
import random
import sys
import time

from construction import (Params, default_layout, build_ops, check_order, run, run_inverse,
                          ideal_T, full_xor, highest_xor, is_bad, apply_op)


def clog2(p):
    return (p - 1).bit_length()


def seg(P, y, i):
    return (y >> P.j(i)) & ((1 << P.K) - 1)


def make(P, layout, u=None, t=None, b=None, x=None, y=None, rng=None):
    st = {}
    for name in layout.order:
        st[name] = rng.getrandbits(layout.width[name]) if layout.width[name] else 0
    for name, v in (("u", u), ("t", t), ("b", b), ("x", x), ("y", y)):
        if v is not None:
            st[name] = v % (1 << layout.width[name])
    return st


def digits_to_int(P, ds):
    return sum(d << (P.G * i) for i, d in enumerate(ds))


def y_from(P, gs, as_, rng, rest=None):
    """y with chosen guard values g_i and parities a_i on the n low segments,
    random (or given) bits elsewhere."""
    y = rng.getrandbits(P.L) if rest is None else rest
    for i in range(P.n):
        m = ((1 << P.K) - 1) << P.j(i)
        y = (y & ~m) | ((2 * gs[i] + as_[i]) << P.j(i))
    return y


def stepwise_model_check(P, layout, ops, st0):
    """On a good address, simulate the integer model alongside the actual
    rotations.  Returns max |g - g0| seen.  Raises on any mismatch."""
    n, G = P.n, P.G
    # integer model state per segment
    v = [seg(P, st0["y"], i) for i in range(n)]
    g0 = [vi >> 1 for vi in v]
    maxdisp = 0
    st = dict(st0)
    # logical content tracking: which physical slot holds t's content etc. is
    # handled by the ops; we just compare y segments after every op with the
    # model, where the model applies the same integer update.
    for op in ops:
        before = dict(st)
        st = apply_op(op, st, layout)
        if op.kind == "rot" and op.target == "y":
            off = op.off(before)  # integer offset before reduction
            # decompose into per-segment integer contributions:
            # off = sum c_i 2^{j_i}; recover c_i by recomputing from labels
            # (the offsets are linear in 2^{j_i}); we verify the segment-wise
            # reading by recomputing each segment directly.
            for i in range(n):
                actual = seg(P, st["y"], i)
                # model: segment i plus its own contribution
                c = contribution(P, op, before, i)
                v[i] = v[i] + c
                if not (0 <= v[i] < (1 << P.K)) or actual != v[i]:
                    raise AssertionError(f"segment {i} carry/borrow at {op.label}: model {v[i]} actual {actual}")
                maxdisp = max(maxdisp, abs((v[i] >> 1) - g0[i]) if v[i] >= 0 else 10**9)
            # untouched bits of y (below j_0 and from j_n upward)
            lowmask = (1 << P.j(0)) - 1
            assert (st["y"] & lowmask) == (st0["y"] & lowmask), "low bits of y changed"
            assert (st["y"] >> P.j(n)) == (st0["y"] >> P.j(n)), "bits >= j_n changed"
        elif op.kind == "rot" and op.target == "b":
            # digit-wise: no carry/borrow between digits of the back field
            off = op.off(before)
            for i in range(n):
                dprev = (before["b"] >> (G * i)) & (P.B - 1)
                dnow = (st["b"] >> (G * i)) & (P.B - 1)
                c = digit_contribution(P, op, before, i)
                if not (0 <= dprev + c < P.B) or dnow != dprev + c:
                    raise AssertionError(f"digit {i} overflow at {op.label}")
    return maxdisp


def contribution(P, op, st, i):
    """Per-segment integer contribution of a y-rotation (from the text's
    formulas), evaluated on the controls `st`."""
    G = P.G
    lab = op.label
    ctrl = "x" if "[x]" in lab else "u"
    z = (st["x"] >> P.j(i)) & 1 if ctrl == "x" else (st["u"] >> (G * i)) & 1
    w = (st["t"] >> (G * i)) & (P.B - 1)
    if lab.endswith("y+=2zw"):
        return 2 * z * w
    if lab.endswith("y+=z(1-2w)"):
        return z * (1 - 2 * w)
    raise ValueError(lab)


def digit_contribution(P, op, st, i):
    G = P.G
    lab = op.label
    yb = (st["y"] >> P.j(i)) & 1
    if "w+=v mod 2" in lab:
        return yb
    if "w-=(v mod2)^z" in lab:
        ctrl = "x" if "[x]" in lab else "u"
        z = (st["x"] >> P.j(i)) & 1 if ctrl == "x" else (st["u"] >> (G * i)) & 1
        return -(yb ^ z)
    if lab.startswith("load u +x"):
        return (st["x"] >> P.j(i)) & 1
    if lab.startswith("load u -x"):
        return -((st["x"] >> P.j(i)) & 1)
    raise ValueError(lab)


def check_one(P, layout, ops, st, stats):
    bad = is_bad(P, st)
    cur = run(ops, st, layout)
    T0 = ideal_T(P, st)
    if not bad:
        assert cur == T0, ("S != T on good address", P, st)
        d = stepwise_model_check(P, layout, ops, st)
        stats["maxdisp"] = max(stats["maxdisp"], d)
        stats["good"] += 1
    else:
        stats["bad"] += 1
        if cur != T0:
            stats["S_ne_T"] += 1
    assert is_bad(P, cur) == bad, "S does not preserve bad set"
    assert is_bad(P, T0) == bad, "T does not preserve bad set"
    inv = run_inverse(ops, cur, layout)
    assert inv == st, "inverse failed"
    final = ideal_T(P, inv) if is_bad(P, cur) else cur
    assert final == T0, "repair failed"
    fin2 = highest_xor(P, final)
    want = full_xor(P, st)
    assert fin2 == want, "full op failed"
    for name in layout.order:
        if name != "y":
            assert fin2[name] == st[name], f"{name} not restored"


def adversarial(P, layout, rng):
    B, K, n = P.B, P.K, P.n
    half = 1 << (K - 1)
    lo, hi = 2 * B, half - 2 * B  # good iff lo <= g < hi
    gvals = sorted({0, 1, max(0, lo - 1), lo, lo + 1, max(0, hi - 1), max(0, hi), hi + 1, half - 1}
                   )
    gvals = [g for g in gvals if 0 <= g < half]
    dvals = sorted(d for d in {0, 1, B - 2, B - 1} if 0 <= d < B)
    out = []
    ones = lambda w: (1 << w) - 1
    nG = n * P.G
    # all ones / all zeros everywhere
    out.append(make(P, layout, u=ones(nG), t=ones(nG), b=ones(nG), x=ones(P.L), y=ones(P.L), rng=rng))
    out.append(make(P, layout, u=0, t=0, b=0, x=0, y=0, rng=rng))
    out.append(make(P, layout, u=0, t=0, b=0, x=ones(P.L), y=0, rng=rng))
    # every combination of a common guard value, common digit values, parities, controls
    for g in gvals:
        for td in dvals:
            for ud in dvals:
                for a in (0, 1):
                    for xb in (0, 1):
                        bd = rng.choice((0, B - 1))
                        t = digits_to_int(P, [td] * n)
                        u = digits_to_int(P, [ud] * n)
                        bb = digits_to_int(P, [bd] * n)
                        x = ones(P.L) if xb else 0
                        y = y_from(P, [g] * n, [a] * n, rng, rest=ones(P.L) if a else 0)
                        out.append(make(P, layout, u=u, t=t, b=bb, x=x, y=y, rng=rng))
    # mixed per-segment extremes
    for _ in range(200):
        gs = [rng.choice(gvals) for _ in range(n)]
        as_ = [rng.getrandbits(1) for _ in range(n)]
        t = digits_to_int(P, [rng.choice(dvals) for _ in range(n)])
        u = digits_to_int(P, [rng.choice(dvals) for _ in range(n)])
        bb = digits_to_int(P, [rng.choice(dvals) for _ in range(n)])
        out.append(make(P, layout, u=u, t=t, b=bb, y=y_from(P, gs, as_, rng), rng=rng))
    # good addresses pushed to every boundary at once
    for _ in range(100):
        gs = [rng.choice([lo, hi - 1]) for _ in range(n)]
        as_ = [rng.getrandbits(1) for _ in range(n)]
        t = digits_to_int(P, [B - 2] * n)
        u = digits_to_int(P, [B - 2] * n)
        out.append(make(P, layout, u=u, t=t, b=ones(nG), x=ones(P.L),
                        y=y_from(P, gs, as_, rng, rest=ones(P.L)), rng=rng))
    return out


PS = (2, 3, 4, 5, 7, 8, 16, 33, 64)


def main():
    budget = float(sys.argv[1]) if len(sys.argv) > 1 else 600.0
    rng = random.Random(20261008)
    t0 = time.time()
    cases = []
    for p in PS:
        l = clog2(p)
        G = 4 * l + 6
        for K in sorted({G + 4 * l + 10, G + 4 * l + 11, G + 4, G + 5, 2 * G + 4 * l + 10}):
            for f in sorted({2, 3, p} & set(range(2, p + 1)) or {2}):
                for rho in sorted({0, K - 1, rng.randrange(K)}):
                    for later in (False, True):
                        fronts = (("u", "t"), ("t", "u")) if rho == K - 1 else (("u", "t"),)
                        for front in fronts:
                            cases.append((p, G, K, f, rho, later, front))
    # small irregular parameters as well
    for G in (1, 2, 3):
        for K in range(2, 12):
            for f in (2, 3, 5):
                for later in (False, True):
                    cases.append((None, G, K, f, K - 1, later, ("u", "t")))
                    cases.append((None, G, K, f, 0, later, ("t", "u")))
    total = dict(good=0, bad=0, S_ne_T=0, maxdisp=0, addresses=0, cases=0)
    worst_ratio = 0.0
    per_case = max(1, int(budget / max(1, len(cases)) * 1))
    for (p, G, K, f, rho, later, front) in cases:
        P = Params(G=G, K=K, f=f, rho=rho, later=later)
        spect = ((0, "s0", 3), (3, "s3", 2), (6, "s6", 5))
        layout = default_layout(P, front=front, spectators=spect)
        ops = build_ops(P, layout)
        check_order(ops, layout)
        stats = dict(good=0, bad=0, S_ne_T=0, maxdisp=0)
        addrs = adversarial(P, layout, rng)
        addrs += [make(P, layout, rng=rng) for _ in range(150)]
        # random good addresses (rejection-free construction)
        B, half = P.B, 1 << (K - 1)
        if half - 2 * B > 2 * B:
            for _ in range(150):
                gs = [rng.randrange(2 * B, half - 2 * B) for _ in range(P.n)]
                t = digits_to_int(P, [rng.randrange(B - 1) for _ in range(P.n)])
                u = digits_to_int(P, [rng.randrange(B - 1) for _ in range(P.n)])
                addrs.append(make(P, layout, t=t, u=u, y=y_from(P, gs, [rng.getrandbits(1) for _ in range(P.n)], rng), rng=rng))
        for st in addrs:
            check_one(P, layout, ops, st, stats)
        total["cases"] += 1
        total["addresses"] += len(addrs)
        for k in ("good", "bad", "S_ne_T"):
            total[k] += stats[k]
        if stats["good"]:
            worst_ratio = max(worst_ratio, stats["maxdisp"] / (2 * P.B))
        total["maxdisp"] = max(total["maxdisp"], stats["maxdisp"])
    print(f"random/adversarial: {total['cases']} parameter cases, {total['addresses']} addresses "
          f"({total['good']} good, {total['bad']} bad, {total['S_ne_T']} bad with S!=T); "
          f"all assertions passed; max observed |g displacement| / (2B) = {worst_ratio:.4f}; "
          f"{time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
