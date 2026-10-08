"""Alternative readings and deliberate mutations.

Two purposes.
 (1) Ambiguity: implement other readings of phrases in the text and report
     whether they fail, with the smallest failing case found.
       B  "packed selected bits" for the t-loads read as sum bit_i 2^i
          (the text says "packed radix-B representation" only for the u-load)
       C  inverse offsets evaluated on the controls of the final address q
          instead of "the current inverse controls"
 (2) Sensitivity: each mutation must be caught by the checks, otherwise the
     checks are too weak to have found a real failure.
"""
import itertools
import sys

import exhaustive as E
from addrmaps import (Params, make_program, run, run_inverse, run_inverse_naive,
                      ideal, top_xor, full_ideal, bad, digit, bit, radixB, at_selected)


def enumerate_states(P, late):
    """Every address in the structured space, small P, as Python ints."""
    xs_sel = range(1 << P.f)
    for y in range(1 << P.W_slot):
        for xs in xs_sel:
            x = sum(((xs >> i) & 1) << P.j[i] for i in range(P.f))
            for t in range(1 << P.W_cmp):
                for b in range(1 << P.W_cmp):
                    for u in (range(1 << P.W_cmp) if late else (0,)):
                        yield dict(x=x, y=y, t=t, b=b, u=u)


def good_first_states(P, late):
    """Addresses whose segments lie in the good guard range (other y bits 0),
    every selected x pattern, every t/u digit pattern except B-1, every b;
    then the full enumeration.  Ordered so the first hit is small."""
    B = P.B
    lo, hi = 2 * B, (1 << (P.K - 1)) - 2 * B
    segvals = [2 * g + a for g in range(lo, hi) for a in (0, 1)]
    digs = [d for d in range(B - 1)]
    cmp_vals = [sum(d << (i * P.G) for i, d in enumerate(ds))
                for ds in itertools.product(digs, repeat=P.n)]
    for segs in itertools.product(segvals, repeat=P.n):
        y = sum(v << P.j[i] for i, v in enumerate(segs))
        for xs in range(1 << P.f):
            x = sum(((xs >> i) & 1) << P.j[i] for i in range(P.f))
            for t in cmp_vals:
                for b in range(1 << P.W_cmp):
                    for u in (cmp_vals if late else (0,)):
                        yield dict(x=x, y=y, t=t, b=b, u=u)
    yield from enumerate_states(P, late)


def first_failure(P, late, ops, inverse=run_inverse, badfn=bad, limit=40000):
    """First failing state (good-range addresses first) for checks C1-C4,C7."""
    for k, st in enumerate(good_first_states(P, late)):
        if k >= limit:
            return None
        out = run(P, st, ops)
        if inverse(P, out, ops) != st:
            return 'C1 inverse', st, out, inverse(P, out, ops)
        b0 = badfn(P, st, late)
        T = ideal(P, st)
        if not b0 and out != T:
            return 'C4 S!=T on good', st, out, T
        if bool(badfn(P, T, late)) != bool(b0) or bool(badfn(P, out, late)) != bool(b0):
            return 'C2/C3 invariance', st, out, T
        rep = ideal(P, inverse(P, out, ops)) if badfn(P, out, late) else out
        if top_xor(P, rep) != full_ideal(P, st):
            return 'C7 repaired', st, top_xor(P, rep), full_ideal(P, st)
    return None


def mutate(ops, which):
    ops = list(ops)
    if which == 'drop_step4':
        i = max(k for k, o in enumerate(ops) if o[0] == 'rot' and o[4].startswith('(4)'))
        return ops[:i - 1] + ops[i + 2:]
    if which == 'step3_uses_old_t':
        # move the (2) load after (3): (3) then sees the unloaded temporary
        out = []
        k = 0
        while k < len(ops):
            o = ops[k]
            if o[0] == 'swap' and k + 1 < len(ops) and ops[k + 1][0] == 'rot' and \
                    ops[k + 1][4].startswith('(2)'):
                blk = ops[k:k + 3]
                out.append(ops[k + 3])
                out.extend(blk)
                k += 4
                continue
            out.append(o)
            k += 1
        return out
    if which == 'no_unload':
        i = max(k for k, o in enumerate(ops) if o[0] == 'rot' and o[4] == 'unload u')
        return ops[:i - 1] + ops[i + 2:]
    raise ValueError(which)


def bad_without_u(P, st, late):
    return bad(P, st, False)


def bad_without_t(P, st, late):
    B = P.B
    res = False
    for i in range(P.n):
        g = ((st['y'] >> P.j[i]) & ((1 << P.K) - 1)) >> 1
        res = res or g < 2 * B or g >= (1 << (P.K - 1)) - 2 * B
        if late:
            res = res or digit(P, st['u'], i) == B - 1
    return res


def main():
    fails_expected_missing = 0
    print("== Reading A (primary): radix-B packing, stepwise inverse ==")
    for P, late in ((Params(3, 6, 0, 2), False), (Params(2, 6, 0, 2), True)):
        r = first_failure(P, late, make_program(late))
        print(f"  {P} late={late}: {'no failure' if r is None else r}")
        if r is not None:
            fails_expected_missing += 1

    print("== Reading B: t-loads packed as sum bit_i 2^i ==")
    for P, late in ((Params(2, 6, 0, 2), False), (Params(3, 5, 0, 1), False),
                    (Params(3, 6, 0, 2), False)):
        r = first_failure(P, late, make_program(late, packing='binary'))
        print(f"  {P} late={late}: {r if r is None else (r[0], r[1])}")
    print("   (identical to A when n=1 or G=1, since then 2^i = B^i; must differ"
          " for n>=2, G>=2)")

    print("== Reading C: inverse offsets read from the final address q ==")
    for P, late in ((Params(2, 6, 0, 2), False), (Params(2, 6, 0, 2), True)):
        r = first_failure(P, late, make_program(late), inverse=run_inverse_naive)
        print(f"  {P} late={late}: {r if r is None else (r[0], r[1])}")
        if r is None:
            fails_expected_missing += 1

    print("== Mutations (each must be detected) ==")
    cases = [('drop_step4', False, bad), ('step3_uses_old_t', False, bad),
             ('no_unload', True, bad),
             ('bad set omits t digits', False, bad_without_t)]
    for name, late, badfn in cases:
        P = Params(2, 6, 0, 2)
        ops = make_program(late)
        if name in ('drop_step4', 'step3_uses_old_t', 'no_unload'):
            ops = mutate(ops, name)
        r = first_failure(P, late, ops, badfn=badfn)
        print(f"  {name:28s} {P} late={late}: "
              f"{'NOT DETECTED' if r is None else 'detected: ' + r[0]}")
        if r is None:
            fails_expected_missing += 1
    # The u-digit exclusion is undetectable at n=1: the only u digit is the
    # top digit, and wrapping B-1 -> 0 mod 2^{nG} still flips its parity, so
    # the two control parities still differ by x.  It matters for n>=2,
    # where a carry from digit 0 flips the parity of digit 1.  Targeted case:
    P = Params(3, 6, 0, 2)
    B = P.B
    y = sum((2 * (2 * B) + 0) << P.j[i] for i in range(P.n))   # g_i = 2B, good
    st = dict(x=1 << P.j[0], y=y, t=0, b=0, u=B - 1)           # u_0 = B-1
    out = run(P, st, make_program(True))
    T = ideal(P, st)
    print(f"  targeted u-carry case {P} late=True state={st}:")
    print(f"     bad (as written) = {bool(bad(P, st, True))}; "
          f"bad without u clause = {bool(bad_without_u(P, st, True))}")
    print(f"     S(y)={out['y']}  T(y)={T['y']}  S==T: {out == T}"
          f"  -> u clause is needed for n>=2 (mutant {'NOT ' if out == T else ''}detected)")
    if out == T:
        fails_expected_missing += 1
    return fails_expected_missing


if __name__ == '__main__':
    sys.exit(1 if main() else 0)
