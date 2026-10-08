"""Reproduce every result in REPORT.md:  nice -n 19 python3 run_all.py

Sections
  E1  exhaustive small shapes x structured/random offset tables
  E2  exhaustive over ALL offset functions for tiny control spaces
  E3  compact-control application offsets (first/second/u-variants/loads/unload)
  E4  randomized larger shapes, adversarial offsets
  S   scaling: per-cell counter cost vs control width; record regime
  X   alternative reading: target field inside the record (outside the lemma)
Exit status nonzero if any correctness or count check fails.
"""
import itertools
import json
import math
import random
import sys
import time

from machine import Layout, two_piece_rotation, reference_rotation
from offsets import make, table_offset

FAIL = []
ROWS = []
# constants for the explicit checks, fixed BEFORE running (not fitted)
DATA_PER_V = 8          # 2 copies x (read+write) + 4 rewinds/clears per cell
STREAM_PER_V = 24       # derived a priori: per pass <= 8V (suffix countdown+reload)
                        # + 4V (block decrements); two passes; plus 8*P*A for
                        # block-countdown underflow walks (one per piece)
FIBER_PER_A2 = 64       # per-fiber offset+init+prefix work / A^2 for app offsets


def A_of(V):
    return math.ceil(math.log2(2 * V))


def check(lay, fn, ref, tag, record_field=None, app=False, keep=False):
    V = lay.V
    data = list(range(V))           # distinct labels: detects any misplacement
    out, cost, st = two_piece_rotation(lay, data, fn)
    exp = reference_rotation(lay, data, ref)
    ok = out == exp
    R = lay.lengths[-1] if record_field is None else record_field
    M = V // R
    A = A_of(V)
    P = st["fibers"]
    row = dict(tag=tag, lengths=lay.lengths, ti=lay.ti, controls=lay.controls,
               V=V, M=M, R=R, A=A, P=P, Q=lay.Q, B=lay.B,
               data=cost.data, stream=cost.stream, fiber=cost.fiber,
               total=cost.total, copies=cost.copies,
               max_offset_cost=cost.max_offset_cost)
    problems = []
    if not ok:
        problems.append("rotation output differs from reference")
    if max(L.bit_length() for L in [lay.lengths[c] - 1 for c in lay.controls] or [0]) > A:
        problems.append("control wider than A")
    if P > M:
        problems.append(f"fibers {P} > records {M}")
    if cost.copies != 2 * V:
        problems.append(f"copies {cost.copies} != 2V")
    if cost.data != DATA_PER_V * V:
        problems.append(f"data moves {cost.data} != 8V")
    if cost.stream > STREAM_PER_V * V + 8 * P * A:
        problems.append(f"stream counter work {cost.stream} > {STREAM_PER_V}V + 8PA")
    if app and cost.max_offset_cost > FIBER_PER_A2 * A * A:
        problems.append("offset cost above 64 A^2")
    if app and cost.fiber > FIBER_PER_A2 * P * A * A:
        problems.append("fiber work above 64 P A^2")
    if app and cost.total > (DATA_PER_V + STREAM_PER_V) * V + 8 * P * A + FIBER_PER_A2 * M * A * A:
        problems.append("total above 32V + 8PA + 64 M A^2")
    row["ok"] = not problems
    if problems:
        FAIL.append((tag, lay.lengths, lay.ti, lay.controls, problems))
    if keep or problems:
        ROWS.append(row)
    return row


def section(name):
    print(f"\n== {name}", flush=True)
    return time.time()


def E1():
    t0 = section("E1 exhaustive small shapes")
    rng = random.Random(1)
    n = 0
    maxs = 0.0
    for k in range(0, 4):
        for pre in itertools.product([1, 2, 3, 4], repeat=k):
            for cmask in range(1 << k):
                ctr = [i for i in range(k) if cmask >> i & 1]
                for Q in [1, 2, 4, 8]:
                    for post in [[], [2], [3]]:
                        for R in [1, 2, 3]:
                            lengths = list(pre) + [Q] + post + [R]
                            lay = Layout(lengths, k, ctr)
                            if lay.V > 4096:
                                continue
                            salt = rng.randrange(1 << 30)
                            tables = [
                                lambda key, Q=Q: 0,
                                lambda key, Q=Q: Q - 1,
                                lambda key, Q=Q: Q,
                                lambda key, Q=Q: -1 - sum(key),
                                lambda key, Q=Q, s=salt: (hash((s,) + key) % (6 * Q + 1)) - 3 * Q,
                                lambda key, Q=Q: sum((i + 1) * v for i, v in enumerate(key)) * 7 + 3,
                            ]
                            for ti_, tab in enumerate(tables):
                                fn, ref = table_offset(tab, ctr)
                                r = check(lay, fn, ref, f"E1.{ti_}")
                                maxs = max(maxs, r["stream"] / r["V"])
                                n += 1
    print(f"cases={n} max stream/V={maxs:.3f} time={time.time()-t0:.0f}s")
    return dict(cases=n, max_stream_per_V=maxs)


def E2():
    t0 = section("E2 all offset functions, tiny control spaces")
    n = 0
    shapes = []
    for Q in [2, 4]:
        for R in [1, 2]:
            shapes += [
                ([4, Q, R], 1, [0]),
                ([2, 2, Q, R], 2, [0, 1]),
                ([2, 2, Q, R], 2, [1]),
                ([3, 2, 2, Q, R], 3, [1, 2]),
                ([2, 3, Q, 2, R], 2, [0]),
                ([3, Q, R], 1, [0]),
            ]
    for lengths, ti, ctr in shapes:
        lay = Layout(lengths, ti, ctr)
        Q = lay.Q
        space = list(itertools.product(*[range(lengths[c]) for c in ctr]))
        if Q ** len(space) > 4096:
            continue
        for vals in itertools.product(range(Q), repeat=len(space)):
            tab = dict(zip(space, vals))
            fn, ref = table_offset(lambda key, tab=tab: tab[key], ctr)
            check(lay, fn, ref, "E2")
            n += 1
    print(f"cases={n} time={time.time()-t0:.0f}s")
    return dict(cases=n)


def app_layouts(kind, n, K, G, R, spec):
    """Physical field orders from the construction. Returns (lengths, ti, idx, W)."""
    fK, nG = (n + 1) * K, n * G
    s = spec
    if kind in ("first", "second"):
        # [S0][t][S1][x][y][S3][rec]  (x precedes y: earlier source)
        L = [s, 1 << nG, s + 1, 1 << fK, 1 << fK, s, R]
        return L, 4, {"t": 1, "x": 3}, fK
    if kind in ("first_u", "second_u"):
        # [u][t][S][y][S][rec]  later source, control u parities
        L = [1 << nG, 1 << nG, s, 1 << fK, s, R]
        return L, 3, {"u": 0, "t": 1}, fK
    if kind == "load_y":
        # [S][y][S][b][rec]  control y (fK bits) wider than target b (nG bits)
        L = [s, 1 << fK, s + 1, 1 << nG, R]
        return L, 3, {"y": 1}, nG
    if kind == "load_x":
        # [S][y][S][x][b][rec]  later source load of x into compact field
        L = [s, 1 << fK, s, 1 << fK, 1 << nG, R]
        return L, 4, {"x": 3}, nG
    if kind == "unload":
        L = [1 << fK, s, 1 << fK, 1 << nG, R]
        return L, 3, {"x": 0, "y": 2}, nG
    if kind == "unload_rev":  # y before x
        L = [1 << fK, s, 1 << fK, 1 << nG, R]
        return L, 3, {"y": 0, "x": 2}, nG
    raise ValueError(kind)


def E3():
    t0 = section("E3 compact-control application offsets")
    n = 0
    skipped = 0
    worst = {}
    for kind in ["first", "second", "first_u", "second_u", "load_y", "load_x", "unload", "unload_rev"]:
        k2 = "unload" if kind == "unload_rev" else kind
        for nn in [1, 2, 3]:
            for K in [1, 2, 3, 4]:
                for G in [1, 2, 3]:
                    for R in [1, 2, 5]:
                        for rho in range(K):
                            for spec in [1, 2]:
                                L, ti, idx, W = app_layouts(kind, nn, K, G, R, spec)
                                V = math.prod(L)
                                if V > 1 << 15:
                                    skipped += 1
                                    continue
                                lay = Layout(L, ti, sorted(idx.values()))
                                fn, ref = make(k2, idx, nn, K, rho, G, W)
                                r = check(lay, fn, ref, f"E3.{kind}", app=True)
                                A = r["A"]
                                w = worst.setdefault(kind, [0, 0, 0])
                                w[0] = max(w[0], r["max_offset_cost"] / A ** 2)
                                w[1] = max(w[1], r["stream"] / r["V"])
                                w[2] = max(w[2], r["P"] / r["M"])
                                n += 1
    for k, w in worst.items():
        print(f"  {k:11s} max offset/A^2={w[0]:.3f} max stream/V={w[1]:.3f} max P/M={w[2]:.3f}")
    print(f"cases={n} skipped(V>2^15)={skipped} time={time.time()-t0:.0f}s")
    return dict(cases=n, skipped=skipped, worst=worst)


def E4():
    t0 = section("E4 randomized larger shapes, adversarial offsets")
    rng = random.Random(4)
    n = 0
    while n < 160:
        k = rng.randrange(0, 5)
        pre = [rng.choice([1, 2, 3, 5, 7, 8, 16, 32]) for _ in range(k)]
        ctr = sorted(rng.sample(range(k), rng.randrange(0, k + 1))) if k else []
        Q = 1 << rng.randrange(0, 6)
        post = [rng.choice([1, 2, 3])] if rng.random() < 0.4 else []
        R = rng.choice([1, 2, 3, 4, 7])
        lengths = pre + [Q] + post + [R]
        lay = Layout(lengths, k, ctr)
        if lay.V > 1 << 16 or lay.V < 64:
            continue
        mode = n % 4
        s = rng.randrange(1 << 30)
        if mode == 0:
            tab = lambda key, Q=Q, s=s: hash((s,) + key) % Q
        elif mode == 1:
            tab = lambda key, Q=Q: Q - 1 if sum(key) % 2 else 0     # max/zero alternate
        elif mode == 2:
            tab = lambda key, Q=Q, s=s: (hash((s,) + key) % 1000003) * Q * 1000 - 7  # huge
        else:
            tab = lambda key, Q=Q, s=s: -(hash((s,) + key) % (5 * Q))                 # negative
        fn, ref = table_offset(tab, ctr)
        check(lay, fn, ref, f"E4.{mode}")
        n += 1
    print(f"cases={n} time={time.time()-t0:.0f}s")
    return dict(cases=n)


def S():
    t0 = section("S scaling")
    out = []
    print("  wide control, Q=2, R=4: control width w; stream/V and fiber/(P A^2)")
    for w in range(1, 14):
        lay = Layout([1 << w, 2, 4], 1, [0])
        fn, ref = table_offset(lambda key: key[0] * 12345 + 1, [0])
        r = check(lay, fn, ref, "S.wide", keep=True)
        line = (w, r["A"], r["stream"] / r["V"], r["fiber"] / (r["P"] * r["A"] ** 2), r["total"] / r["V"])
        out.append(("wide",) + line)
        print("   w=%2d A=%2d stream/V=%.3f fiber/(P A^2)=%.3f total/V=%.2f" % line)
    print("  application load_y, n=1, K=G=1..: record length growth (record regime)")
    for R in [1, 2, 4, 8, 16, 32, 64, 128, 256]:
        L, ti, idx, W = app_layouts("load_y", 2, 2, 2, R, 1)
        lay = Layout(L, ti, sorted(idx.values()))
        fn, ref = make("load_y", idx, 2, 2, 1, 2, W)
        r = check(lay, fn, ref, "S.record", app=True, keep=True)
        line = (R, r["A"], r["P"], r["M"], r["fiber"] / r["V"], r["total"] / r["V"])
        out.append(("record",) + line)
        print("   R=%3d A=%2d P=%5d M=%6d fiber/V=%.3f total/V=%.3f" % line)
    print(f"time={time.time()-t0:.0f}s")
    return out


def X():
    t0 = section("X alternative reading: target inside the record (not the lemma's setting)")
    out = []
    for R1 in [1, 2, 4, 8, 16, 32]:
        # records of R = R1*2*2 bits regarded as fields [R1][Q=2][2]; target inside.
        c = 64
        lengths = [c, R1, 2, 2]
        R = R1 * 4
        lay = Layout(lengths, 2, [0])
        fn, ref = table_offset(lambda key: key[0], [0])
        V = lay.V
        data = list(range(V))
        o, cost, st = two_piece_rotation(lay, data, fn)
        ok = o == reference_rotation(lay, data, ref)
        M = V // R
        A = A_of(V)
        line = (R, st["fibers"], M, st["fibers"] / M, cost.fiber / (M * A * A), ok)
        out.append(line)
        print("   R=%3d fibers=%5d records=%4d fibers/records=%5.1f fiber/(M A^2)=%.3f correct=%s" % line)
    print(f"time={time.time()-t0:.0f}s")
    return out


if __name__ == "__main__":
    T0 = time.time()
    res = dict(E1=E1(), E2=E2(), E3=E3(), E4=E4(), S=S(), X=X())
    res["failures"] = FAIL
    with open("results.json", "w") as fh:
        json.dump(res, fh, indent=1, default=str)
    print(f"\nTOTAL failures={len(FAIL)} time={time.time()-T0:.0f}s")
    for f in FAIL[:20]:
        print("  FAIL", f)
    sys.exit(1 if FAIL else 0)
