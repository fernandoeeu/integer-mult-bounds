"""(1) The four-update integer identity, exhaustively on a box of integers.
(2) The bad fraction at the proposition's parameters, exactly, against the
    union bound delta = min{1, n(k 2^-G + 8 2^(G-K))} and against 5/(128 p^3).
"""
import sys
from fractions import Fraction


def identity_check(R=64):
    bad = 0
    for v in range(-R, R + 1):
        for w in range(-R, R + 1):
            for z in (0, 1):
                a = v % 2
                v1 = v + 2 * z * w
                assert v1 % 2 == a
                w1 = w + (v1 % 2)
                v2 = v1 + z * (1 - 2 * w1)
                w2 = w1 - ((v2 % 2) ^ z)
                if (v2, w2) != (v + z * (1 - 2 * a), w):
                    bad += 1
    # contrast: the misreading in which the third update uses the ORIGINAL w
    mis = 0
    for v in range(-R, R + 1):
        for w in range(-R, R + 1):
            z = 1
            a = v % 2
            v1 = v + 2 * z * w
            w1 = w + (v1 % 2)
            v2 = v1 + z * (1 - 2 * w)
            w2 = w1 - ((v2 % 2) ^ z)
            if (v2, w2) != (v + z * (1 - 2 * a), w):
                mis += 1
    return bad, mis, (2 * R + 1) ** 2 * 2


def clog2(p):
    return (p - 1).bit_length()


def exact_fraction(G, K, n, k):
    B = 1 << G
    half = 1 << (K - 1)
    good_g = max(0, half - 4 * B)
    return 1 - Fraction(B - 1, B) ** (k * n) * Fraction(good_g, half) ** n


def union(G, K, n, k):
    return min(Fraction(1), n * (Fraction(k, 1 << G) + Fraction(8 << G, 1 << K)))


def main():
    b, mis, tot = identity_check()
    print(f"four-update identity on |v|,|w|<=64, z in {{0,1}}: {tot} cases, {b} failures "
          f"(misreading 'third update uses original w': {mis} failures among z=1 cases)")
    worst = Fraction(0)
    worst_union = Fraction(0)
    rows = 0
    for p in list(range(2, 513)) + [1000, 1023, 1024, 1025, 4096, 65537]:
        l = clog2(p)
        G = 4 * l + 6
        Kc = G + 4 * l + 10
        target = Fraction(5, 128 * p ** 3)
        for k in (1, 2):
            n = p - 1  # f = p, the largest allowed
            u = union(G, Kc, n, k)
            assert u <= target, (p, k, u, target)
            worst_union = max(worst_union, u / target)
            if p <= 300:
                e = exact_fraction(G, Kc, n, k)
                assert e <= u
                worst = max(worst, e / target)
            rows += 1
    print(f"bad fraction at the cutoff K = G + 4l + 10, f = p, both source orders, {rows} (p, order) rows: "
          f"union bound <= 5/(128p^3) everywhere (max ratio {float(worst_union):.6f}); "
          f"exact fraction (p <= 300) max ratio to 5/(128p^3) = {float(worst):.6f}")
    # union bound vs p for f <= p, beyond the cutoff (K larger): monotone
    for p in (2, 3, 5, 17, 100):
        l = clog2(p)
        G = 4 * l + 6
        for K in range(G + 4 * l + 10, G + 4 * l + 40):
            for f in range(2, p + 1):
                for k in (1, 2):
                    assert union(G, K, f - 1, k) <= Fraction(5, 128 * p ** 3)
    print("union bound <= 5/(128p^3) for all 2 <= f <= p, K in [cutoff, cutoff+30), p in {2,3,5,17,100}")
    # just below the cutoff the stated bound can fail (expected: it is only claimed beyond it)
    below = []
    for p in (2, 4, 8, 16, 1024):
        l = clog2(p)
        G = 4 * l + 6
        K = G + 4 * l + 9
        e = exact_fraction(G, K, p - 1, 2)
        below.append((p, float(e / Fraction(5, 128 * p ** 3))))
    print("exact/(5/(128p^3)) one bit below the cutoff (later source, f=p):",
          ", ".join(f"p={p}: {r:.3f}" for p, r in below))


if __name__ == "__main__":
    main()
