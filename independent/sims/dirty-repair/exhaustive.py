"""Exhaustive verification of the compact dirty-control construction and its
deterministic repair at small parameters (numpy, vectorised).

For each parameter set every combination of the enumerated address bits is
tested.  'full' mode enumerates every bit of u, t, b, x, y (and of any
spectators); 'xsel' mode enumerates every bit of u, t, b, y and only the f
selected bits of x (the other x bits are fixed to a random value; no
operation reads them, which the precedence/reads declarations make
explicit and the 'full' runs confirm at smaller sizes).

Checks, for every initial address q:
  A  q good  =>  S(q) == T(q)              (agreement off the bad set)
  B  bad(S q) == bad(q) and bad(T q) == bad(q)   (S and T preserve the bad set)
  C  S^{-1}(S q) == q, with S^{-1} computed by reversing the operations and
     evaluating each inverse offset on the current controls
  D  repair: final(q) = T(S^{-1}(S q)) if S q is bad else S q;  final == T q,
     and after the elementary highest-position XOR it equals the full
     selected-bit addition with u, t, b, x and spectators restored exactly
  E  (small cases) destination ranks of the extracted bad records are
     distinct and equal the set of hole ranks
Also recorded: |bad|, |{S != T}|, the exact bad fraction against the union
bound delta = min{1, n(k 2^-G + 8 2^(G-K))}, and failures of a WRONG
inverse reading (all offsets on the pre-inversion controls) for contrast.
"""
import zlib
import json
import sys
import time
from fractions import Fraction

import numpy as np

from construction import (Params, default_layout, build_ops, check_order, run,
                          run_inverse, run_inverse_final_controls, ideal_T,
                          full_xor, highest_xor, is_bad, rank)

CHUNK = 1 << 21


def free_bits(P, layout, mode):
    """List of (field, bit position) pairs enumerated exhaustively."""
    fb = []
    for name in layout.order:
        w = layout.width[name]
        if name == "u" and not P.later and mode == "xsel":
            # u is an unused spectator for an earlier source; still enumerate
            # it when cheap (it is part of 'arbitrary spectators')
            pass
        if name == "x" and mode == "xsel":
            fb += [("x", P.j(i)) for i in range(P.f)]
        else:
            fb += [(name, k) for k in range(w)]
    return fb


def union_delta(P):
    k = 2 if P.later else 1
    if P.n == 0:
        return Fraction(0)
    return min(Fraction(1), P.n * (Fraction(k, P.B) + Fraction(8 * P.B, 1 << P.K)))


def exact_bad_fraction(P):
    """Exact fraction from independence of the complete fields."""
    if P.n == 0:
        return Fraction(0)
    B = P.B
    half = 1 << (P.K - 1)
    good_g = max(0, (half - 2 * B) - 2 * B)
    pg = Fraction(good_g, half)
    pd = Fraction(B - 1, B)
    k = 2 if P.later else 1
    return 1 - (pd ** (k * P.n)) * (pg ** P.n)


def verify(P, front=("u", "t"), spectators=(), mode="full", seed=0, small_rank_check=None):
    layout = default_layout(P, front=front, spectators=spectators)
    ops = build_ops(P, layout)
    check_order(ops, layout)
    rng = np.random.default_rng(seed)
    base = {name: int(rng.integers(0, 1 << layout.width[name])) for name in layout.order}
    fb = free_bits(P, layout, mode)
    for name, pos in fb:
        base[name] &= ~(1 << pos)
    total_bits = len(fb)
    N = 1 << total_bits
    if small_rank_check is None:
        small_rank_check = total_bits <= 22
    stats = dict(addresses=N, bad=0, S_ne_T=0, S_ne_T_good=0, badS_mismatch=0,
                 badT_mismatch=0, inverse_fail=0, repair_fail=0, full_fail=0,
                 restore_fail=0, wrong_inverse_fail=0)
    hole_ranks, dest_ranks = [], []
    for start in range(0, N, CHUNK):
        idx = np.arange(start, min(N, start + CHUNK), dtype=np.int64)
        st = {name: np.full(idx.shape, base[name], dtype=np.int64) for name in layout.order}
        for s, (name, pos) in enumerate(fb):
            st[name] |= ((idx >> s) & 1) << pos
        bad0 = is_bad(P, st)
        cur = run(ops, st, layout)
        T0 = ideal_T(P, st)
        neq = np.zeros(idx.shape, dtype=bool)
        for name in layout.order:
            neq |= cur[name] != T0[name]
        stats["bad"] += int(bad0.sum())
        stats["S_ne_T"] += int(neq.sum())
        stats["S_ne_T_good"] += int((neq & ~bad0).sum())
        bad_cur = is_bad(P, cur)
        stats["badS_mismatch"] += int((bad_cur != bad0).sum())
        stats["badT_mismatch"] += int((is_bad(P, T0) != bad0).sum())
        inv = run_inverse(ops, cur, layout)
        f_inv = np.zeros(idx.shape, dtype=bool)
        for name in layout.order:
            f_inv |= inv[name] != st[name]
        stats["inverse_fail"] += int(f_inv.sum())
        dest = ideal_T(P, inv)
        final = {name: np.where(bad_cur, dest[name], cur[name]) for name in layout.order}
        f_rep = np.zeros(idx.shape, dtype=bool)
        for name in layout.order:
            f_rep |= final[name] != T0[name]
        stats["repair_fail"] += int(f_rep.sum())
        fin2 = highest_xor(P, final)
        want = full_xor(P, st)
        f_full = np.zeros(idx.shape, dtype=bool)
        f_rest = np.zeros(idx.shape, dtype=bool)
        for name in layout.order:
            f_full |= fin2[name] != want[name]
            if name != "y":
                f_rest |= fin2[name] != st[name]
        stats["full_fail"] += int(f_full.sum())
        stats["restore_fail"] += int(f_rest.sum())
        winv = run_inverse_final_controls(ops, cur, layout)
        f_w = np.zeros(idx.shape, dtype=bool)
        for name in layout.order:
            f_w |= winv[name] != st[name]
        stats["wrong_inverse_fail"] += int(f_w.sum())
        if small_rank_check:
            hole_ranks.append(rank(layout, {k: v[bad_cur] for k, v in cur.items()}))
            dest_ranks.append(rank(layout, {k: v[bad_cur] for k, v in dest.items()}))
    if small_rank_check:
        h = np.sort(np.concatenate(hole_ranks))
        d = np.sort(np.concatenate(dest_ranks))
        stats["holes_filled_exactly"] = bool(h.shape == d.shape and np.array_equal(h, d)
                                             and (d.size < 2 or np.all(np.diff(d) > 0)))
    meas = Fraction(stats["bad"], N)
    stats["bad_fraction"] = float(meas)
    stats["bad_fraction_exact_formula_match"] = (meas == exact_bad_fraction(P))
    stats["union_delta"] = float(union_delta(P))
    stats["bad_le_delta"] = meas <= union_delta(P)
    stats["ops"] = (sum(o.kind == "swap" for o in ops), sum(o.kind == "rot" for o in ops))
    ok = (stats["S_ne_T_good"] == 0 and stats["badS_mismatch"] == 0 and stats["badT_mismatch"] == 0
          and stats["inverse_fail"] == 0 and stats["repair_fail"] == 0 and stats["full_fail"] == 0
          and stats["restore_fail"] == 0 and stats.get("holes_filled_exactly", True)
          and stats["bad_fraction_exact_formula_match"] and stats["bad_le_delta"])
    return ok, stats, layout


def configs(level):
    """(G, K, f, mode).  Enumerated bits: full = 3nG + 2fK (+ spectators),
    xsel = 3nG + fK + f.  Level 0 keeps a single run well under 20 minutes;
    level 1 adds a few 25-27 bit sets at the extreme rho only."""
    if level == 0:
        return [(1, 3, 2, "full"), (1, 4, 2, "full"), (2, 3, 2, "full"), (2, 4, 2, "full"),
                (1, 5, 2, "full"), (1, 3, 3, "full")]
    if level == 1:
        return [(1, 5, 2, "xsel"), (1, 6, 2, "xsel"), (1, 7, 2, "xsel"), (2, 6, 2, "xsel"),
                (2, 7, 2, "xsel"), (1, 4, 3, "xsel")]
    if level == 2:
        return [(2, 8, 2, "xsel"), (1, 5, 3, "xsel")]
    if level == 3:
        return [(1, 6, 3, "xsel")]
    return [(3, 8, 2, "xsel"), (1, 3, 4, "xsel")]


def main():
    level = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    results = []
    all_ok = True
    t0 = time.time()
    for (G, K, f, mode) in configs(level):
        for later in (False, True):
            P0 = Params(G=G, K=K, f=f, rho=0, later=later)
            nb = 3 * P0.n * G + (2 * f * K if mode == "full" else f * K + f)
            spect = tuple((k, f"s{k}", 1) for k in range(0, 6)) if nb <= 15 else ()
            nb += len(spect)
            if level <= 2:
                if nb <= 21:
                    plan = [(r, fr) for r in range(K) for fr in (("u", "t"), ("t", "u"))]
                else:
                    plan = [(0, ("u", "t")), (K - 1, ("u", "t")), (K - 1, ("t", "u"))]
                    if nb <= 22:
                        plan.insert(1, (1, ("u", "t")))
            else:
                plan = [(K - 1, ("u", "t"))]
            for rho, front in plan:
                P = Params(G=G, K=K, f=f, rho=rho, later=later)
                ok, st, layout = verify(P, front=front, spectators=spect, mode=mode,
                                        seed=zlib.crc32(repr((G, K, f, rho, later, front)).encode()))
                all_ok &= ok
                rec = dict(G=G, K=K, f=f, rho=rho, later=later, front="".join(front),
                           mode=mode, layout=" ".join(layout.order), ok=ok, **st)
                results.append(rec)
                print(("OK  " if ok else "FAIL"),
                      f"G={G} K={K} f={f} rho={rho} {'later  ' if later else 'earlier'} "
                      f"front={''.join(front)} {mode:4s} N=2^{st['addresses'].bit_length()-1} "
                      f"bad={st['bad_fraction']:.4f} delta={st['union_delta']:.4f} "
                      f"S!=T={st['S_ne_T']} S!=T&good={st['S_ne_T_good']} "
                      f"wrongInv={st['wrong_inverse_fail']}"
                      + (f" holes={st['holes_filled_exactly']}" if 'holes_filled_exactly' in st else ""),
                      flush=True)
    with open(f"results/exhaustive_level{level}.json", "w") as fh:
        json.dump(results, fh, indent=1, default=str)
    print(f"exhaustive: {len(results)} parameter sets, "
          f"{sum(r['addresses'] for r in results)} addresses, all_ok={all_ok}, "
          f"{time.time() - t0:.0f}s")
    sys.exit(0 if all_ok else 1)


if __name__ == "__main__":
    main()
