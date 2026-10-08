"""Exact dimension of U(A_C) = span{t_T : T five-set containing C} in Q^h at h=28,
for every pair C: lower bound rank mod p (p = 2^61-1) <= rank over Q; upper
bound h-2 from the two independent integer functionals u_a - u_b and
sum(u) - 5 u_a vanishing on every vector."""
from itertools import combinations
import sys
h = int(sys.argv[1]) if len(sys.argv) > 1 else 28
p = (1 << 61) - 1


def rank_mod(vecs):
    piv = {}
    for u in vecs:
        u = [x % p for x in u]
        for c in sorted(piv):
            if u[c]:
                r = piv[c]; f = u[c]
                u = [(x - f * y) % p for x, y in zip(u, r)]
        nz = next((i for i, x in enumerate(u) if x), None)
        if nz is not None:
            inv = pow(u[nz], -1, p); u = [x * inv % p for x in u]
            piv[nz] = u
    return len(piv)


dims = set()
for C in [(0, 1), (0, 2), (5, 17), (h - 2, h - 1)]:
    vecs = [[1 if i in C or i in U else 0 for i in range(h)] for U in combinations([x for x in range(h) if x not in C], 3)]
    a, b = C
    assert all(u[a] == u[b] and sum(u) == 5 * u[a] for u in vecs)
    dims.add(rank_mod(vecs))
print('h', h, 'retained span rank mod p over sample pairs:', dims, '; upper bound h-2 =', h - 2,
      '; exact dim = h-2:', dims == {h - 2})
