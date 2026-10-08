"""Exact linear algebra over F_2 with vectors stored as Python ints.

The bilinear form is the standard dot product: x.y = popcount(x & y) mod 2.
On a tensor power with product coordinates this is exactly the tensor form.
Every pass/fail decision in this project goes through these routines.
"""


def dot(x, y):
    return (x & y).bit_count() & 1


def norm(x):
    return x.bit_count() & 1


class Space:
    """A subspace of F_2^n kept as a fully reduced echelon basis."""

    __slots__ = ("n", "piv", "pmask")

    def __init__(self, n, vectors=()):
        self.n = n
        self.piv = {}  # pivot bit -> vector, fully reduced
        self.pmask = 0
        for v in vectors:
            self.add(v)

    def reduce(self, x):
        # fully reduced echelon form: each basis vector contains exactly one
        # pivot bit, so one pass over the pivot bits present in x suffices
        piv = self.piv
        m = x & self.pmask
        while m:
            b = m.bit_length() - 1
            x ^= piv[b]
            m ^= 1 << b
        return x

    def add(self, v):
        r = self.reduce(v)
        if not r:
            return False
        b = r.bit_length() - 1
        # keep full reduction: eliminate bit b from others
        for k, w in list(self.piv.items()):
            if (w >> b) & 1:
                self.piv[k] = w ^ r
        self.piv[b] = r
        self.pmask |= 1 << b
        return True

    def contains(self, x):
        return self.reduce(x) == 0

    def dim(self):
        return len(self.piv)

    def basis(self):
        return list(self.piv.values())

    def key(self):
        return tuple(sorted(self.piv.values()))

    def contains_space(self, other):
        return all(self.contains(v) for v in other.piv.values())

    def __eq__(self, other):
        return self.n == other.n and self.key() == other.key()

    def __hash__(self):
        return hash(self.key())


def perp(U, within=None):
    """Orthogonal complement of U inside `within` (default: whole F_2^n)."""
    n = U.n
    ub = U.basis()
    if within is None:
        # solve x.u = 0 for all u in U: kernel of the matrix with rows ub
        return kernel(ub, n)
    wb = within.basis()
    # x = sum c_k w_k ; need sum c_k (w_k.u_j) = 0 for all j
    k = len(wb)
    rows = []
    for u in ub:
        r = 0
        for i, w in enumerate(wb):
            if dot(w, u):
                r |= 1 << i
        rows.append(r)
    coeffs = kernel(rows, k)
    out = Space(n)
    for c in coeffs.basis():
        x = 0
        i = 0
        while c:
            if c & 1:
                x ^= wb[i]
            c >>= 1
            i += 1
        out.add(x)
    return out


def kernel(rows, n):
    """Kernel {x in F_2^n : r.x = 0 for every row r}."""
    R = Space(n, rows)
    piv = R.piv  # fully reduced: each pivot bit appears only in its own row
    free = [b for b in range(n) if b not in piv]
    out = Space(n)
    for f in free:
        x = 1 << f
        for b, r in piv.items():
            if (r >> f) & 1:
                x |= 1 << b
        out.add(x)
    return out


def gram_rank(vectors):
    rows = []
    for x in vectors:
        r = 0
        for j, y in enumerate(vectors):
            if dot(x, y):
                r |= 1 << j
        rows.append(r)
    return Space(len(vectors), rows).dim()


def nondegenerate(U):
    b = U.basis()
    return gram_rank(b) == len(b)


def nonalternating(U):
    return any(norm(v) for v in U.basis())


def orthonormal_basis(U):
    """Construct an orthonormal basis of a nondegenerate nonalternating space
    following the upstream absorption argument, or return None."""
    if U.dim() == 0:
        return []
    if not nondegenerate(U) or not nonalternating(U):
        return None
    n = U.n
    units = []
    rest = U
    # split off unit lines while the remainder is nonalternating
    while rest.dim() > 0:
        u = next((v for v in rest.basis() if norm(v)), None)
        if u is None:
            # rest is a nondegenerate alternating space; pick a vector with
            # norm one in the span if any (impossible) -> absorb planes
            break
        units.append(u)
        rest = perp(Space(n, [u]), within=rest)
    # absorb alternating planes
    while rest.dim() > 0:
        bs = rest.basis()
        a = bs[0]
        b = next(y for y in bs if dot(a, y))
        w = units.pop()
        units.extend([w ^ a, w ^ b])
        units.append(w ^ a ^ b)
        # keep the last absorbed unit as the new w (it is last in list)
        rest = perp(Space(n, [a, b]), within=rest)
    return units


def check_orthonormal(basis, U):
    if len(basis) != U.dim():
        return False
    for i, x in enumerate(basis):
        if not U.contains(x):
            return False
        for j, y in enumerate(basis):
            if dot(x, y) != (1 if i == j else 0):
                return False
    return Space(U.n, basis).dim() == U.dim()


def residual(U, V):
    """Orthogonal residual of U inside V (requires U subset V)."""
    return perp(U, within=V)
