"""Second derivation, in exact rational linear algebra, of the frame conditions
on dumped small-h merged graphs (produced by `bun src/main.ts --dump=out/graphs`).

Independent of the TS support logic: it recomputes node spans U_z in F = Q^h
from source indicators and checks, with the form B = I - J/9:
  * U_z is positive definite (Gram matrix of a basis has positive leading minors)
  * U_z^perp is nondegenerate (restricted Gram matrix of a basis is invertible)
  * forward: U_child within U_parent on every edge (rank test)
  * reverse: U_parent^perp within U_child^perp on every edge
  * outputs: U_z within t_T^perp (B(u, t_T) = 0 on a basis), equivalently the
    physical X line <t_T> lies in U_z^perp
  * inputs: U_input^perp = t_S^perp exactly
Usage: python3 -I la_check.py out/graphs/*.json
"""
import json
import sys
from fractions import Fraction as Fr


def form(h, x, y):
    return sum(a * b for a, b in zip(x, y)) - sum(x) * sum(y) / Fr(9)


def basis(vecs):
    """Row-reduced basis (list of Fraction vectors) of the span."""
    rows = []
    pivots = []
    for v in vecs:
        v = list(v)
        for r, p in zip(rows, pivots):
            if v[p] != 0:
                f = v[p] / r[p]
                v = [a - f * b for a, b in zip(v, r)]
        nz = next((j for j, a in enumerate(v) if a != 0), None)
        if nz is not None:
            rows.append(v)
            pivots.append(nz)
    return rows


def rank(vecs):
    return len(basis(vecs))


def det(M):
    M = [list(r) for r in M]
    n = len(M)
    d = Fr(1)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None:
            return Fr(0)
        if p != c:
            M[c], M[p] = M[p], M[c]
            d = -d
        d *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            M[r] = [a - f * b for a, b in zip(M[r], M[c])]
    return d


def perp(h, U):
    """Basis of U^perp w.r.t. B: solve B u . x = 0 for u in basis(U)."""
    Bu = []
    for u in U:
        s = sum(u)
        Bu.append([u[j] - s / Fr(9) for j in range(h)])
    # null space of matrix with rows Bu
    rows = basis(Bu)
    # reduced row echelon
    piv = []
    R = []
    for r in rows:
        R.append(r)
    # full RREF
    m = [list(r) for r in R]
    lead = 0
    pcols = []
    rcount = len(m)
    for r in range(rcount):
        while lead < h and all(m[i][lead] == 0 for i in range(r, rcount)):
            lead += 1
        if lead >= h:
            break
        i = next(i for i in range(r, rcount) if m[i][lead] != 0)
        m[r], m[i] = m[i], m[r]
        lv = m[r][lead]
        m[r] = [a / lv for a in m[r]]
        for i in range(rcount):
            if i != r and m[i][lead] != 0:
                f = m[i][lead]
                m[i] = [a - f * b for a, b in zip(m[i], m[r])]
        pcols.append(lead)
        lead += 1
    free = [j for j in range(h) if j not in pcols]
    out = []
    for f in free:
        v = [Fr(0)] * h
        v[f] = Fr(1)
        for r, pc in enumerate(pcols):
            v[pc] = -m[r][f]
        out.append(v)
    return out


def contains(A, B):
    """span(B) within span(A)"""
    return rank(A + B) == rank(A)


def check(path):
    g = json.load(open(path))
    h = g["h"]
    trips = g["triples"]
    NT = len(trips)
    ind = []
    for t in trips:
        v = [Fr(0)] * h
        for p in t:
            v[p] = Fr(1)
        ind.append(v)
    left, right = g["left"], g["right"]
    span = {}
    for t in range(NT):
        span[t] = [ind[t]]
    for k in range(len(left)):
        span[NT + k] = basis(span[left[k]] + span[right[k]])
    perps = {}
    ok = dict(pd=True, perpNondeg=True, fwd=True, rev=True, outOrth=True, inputPerp=True)
    for z, U in span.items():
        G = [[form(h, a, b) for b in U] for a in U]
        if any(det([row[:j] for row in G[:j]]) <= 0 for j in range(1, len(U) + 1)):
            ok["pd"] = False
        Pz = perp(h, U)
        perps[z] = Pz
        if Pz:
            Gp = [[form(h, a, b) for b in Pz] for a in Pz]
            if det(Gp) == 0:
                ok["perpNondeg"] = False
    for k in range(len(left)):
        w = NT + k
        for ch in (left[k], right[k]):
            if not contains(span[w], span[ch]):
                ok["fwd"] = False
            if not contains(perps[ch], perps[w]):
                ok["rev"] = False
    for z, T in zip(g["outNode"], g["outTarget"]):
        tT = ind[T]
        if any(form(h, u, tT) != 0 for u in span[z]):
            ok["outOrth"] = False
        if not contains(perps[z], [tT]):
            ok["outOrth"] = False
    for t in range(NT):
        tp = perp(h, [ind[t]])
        if not (contains(tp, perps[t]) and contains(perps[t], tp)):
            ok["inputPerp"] = False
    allok = all(ok.values())
    print(f"{path}: nodes={len(span)} " + " ".join(f"{k}={v}" for k, v in ok.items()) + (" PASS" if allok else " FAIL"))
    return allok


if __name__ == "__main__":
    res = [check(p) for p in sys.argv[1:]]
    print("LA OVERALL:", "PASS" if all(res) else "FAIL")
    sys.exit(0 if all(res) else 1)
