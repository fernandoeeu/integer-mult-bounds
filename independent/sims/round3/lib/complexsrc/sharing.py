"""PR 4 stage-1 / stage-3 bank sharing: (A,B) at stage 1 <-> (B, pi(A)) at
stage 3.  Checks the joining edge E -> H as actual subspaces of F^{(x)3}."""
import random
from f2 import Space, perp, residual, nondegenerate, nonalternating, orthonormal_basis, check_orthonormal
from tensor import tens, tens2
from circuit import triples
from network import walk, F_KEY, Z_KEY


def pi_list(h):
    T, idx = triples(h)
    out = []
    for t in T:
        u = 0
        for p in range(h):
            if t >> p & 1:
                u |= 1 << (p ^ 1)
        out.append(idx[u])
    return T, out


def combinatorics(h):
    T, pi = pi_list(h)
    bij = sorted(pi) == list(range(len(T)))
    inter = set((T[i] & T[pi[i]]).bit_count() for i in range(len(T)))
    return dict(bijection=bij, intersections=sorted(inter), even=all(x % 2 == 0 for x in inter))


def join_check(h, pairs):
    T, pi = pi_list(h)
    m = h ** 3
    F = [1 << i for i in range(h)]
    res = []
    for A, B in pairs:
        tA, tB, tpA = T[A], T[B], T[pi[A]]
        E = Space(m, [tens(f, tA, tB, h) for f in F])
        # H = (<tB (x) tpiA>)^perp (x) F
        p = 0
        for i in range(h):
            if tB >> i & 1:
                for j in range(h):
                    if tpA >> j & 1:
                        p |= 1 << (i * h + j)
        Bperp = perp(Space(h * h, [p])).basis()
        H = Space(m, [tens2(b, f, h) for b in Bperp for f in F])
        inc = H.contains_space(E)
        R = residual(E, H) if inc else None
        ok = (inc and nondegenerate(E) and nondegenerate(H) and R.dim() == m - 2 * h
              and nondegenerate(R) and nonalternating(R))
        onb = None
        if ok:
            ob = orthonormal_basis(R)
            onb = ob is not None and check_orthonormal(ob, R)
        res.append((A, B, ok, onb))
    return res


def endpoint_frames(inv1, inv3):
    """Every auxiliary role must end stage 1 at D_1 and start stage 3 at D_0."""
    s1, s3 = walk(inv1), walk(inv3)
    bad = []
    for w in range(2 * inv1.v + inv1.nc, inv1.nw):
        last = s1[w][-1][0]
        first = s3[w][0][0]
        if last != (F_KEY, F_KEY) or first != (F_KEY, Z_KEY):
            bad.append((w, last, first))
    return bad
