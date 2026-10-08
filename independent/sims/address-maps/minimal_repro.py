"""Standalone minimal cases (no imports from this directory).

None of these is a failure of the construction as written.  They show that
two phrases of the text carry weight, i.e. that the natural misreadings fail,
and that the u-digit clause of the bad set is necessary once n >= 2.

  Case B  "rotate the back field by the packed selected bits of the current y"
          read as sum y_{j_i} 2^i instead of radix-B sum y_{j_i} B^i.
  Case C  "Every inverse offset is evaluated on the current inverse controls"
          replaced by evaluating each inverse offset on the final address.
  Case U  later source, u digit 0 equal to B-1, with the u clause removed
          from the bad set: the address would be classified good but S != T.
"""


def run(f, K, rho, G, st, late, packing='radixB', inverse=False, naive=False):
    n, B = f - 1, 1 << G
    j = [rho + i * K for i in range(f)]
    Wy, Wc = f * K, n * G
    bit = lambda v, p: (v >> p) & 1
    dig = lambda v, i: (v >> (i * G)) & (B - 1)
    pk = (lambda c: sum(ci << (i * G) for i, ci in enumerate(c))) if packing == 'radixB' \
        else (lambda c: sum(ci << i for i, ci in enumerate(c)))
    ops = []

    def four(zs):
        z = (lambda s: [bit(s['x'], j[i]) for i in range(n)]) if zs == 'x' else \
            (lambda s: [dig(s['u'], i) & 1 for i in range(n)])
        ops.append(('y', lambda s: sum((2 * z(s)[i] * dig(s['t'], i)) << j[i] for i in range(n))))
        ops.extend([('swap', 't'), ('b', lambda s: pk([bit(s['y'], j[i]) for i in range(n)])), ('swap', 't')])
        ops.append(('y', lambda s: sum((z(s)[i] * (1 - 2 * dig(s['t'], i))) << j[i] for i in range(n))))
        ops.extend([('swap', 't'), ('b', lambda s: -pk([bit(s['y'], j[i]) ^ z(s)[i] for i in range(n)])),
                ('swap', 't')])

    def load(sg):
        ops.extend([('swap', 'u'),
                    ('b', lambda s: sg * sum(bit(s['x'], j[i]) << (i * G) for i in range(n))),
                    ('swap', 'u')])
    if late:
        four('u'); load(1); four('u'); load(-1)
    else:
        four('x')
    s = dict(st)
    q = dict(st)
    seq = reversed(ops) if inverse else ops
    for tgt, fn in seq:
        if tgt == 'swap':
            s['b'], s[fn] = s[fn], s['b']
            continue
        off = fn(q if naive else s)
        s[tgt] = (s[tgt] + (-off if inverse else off)) % (1 << (Wy if tgt == 'y' else Wc))
    return s


def ideal(f, K, rho, st):
    n = f - 1
    m = sum(((st['x'] >> (rho + i * K)) & 1) << (rho + i * K) for i in range(n))
    return dict(st, y=st['y'] ^ m)


print("Case B: f=3,K=6,rho=0,G=2 (B=4), earlier source, address is good")
st = dict(x=1, y=1104, t=0, b=0, u=0)          # segments g_0=g_1=8=2B, x_{j_0}=1
print("  input            ", st)
print("  expected T(a)    ", ideal(3, 6, 0, st))
print("  radix-B reading  ", run(3, 6, 0, 2, st, False))
print("  2^i reading      ", run(3, 6, 0, 2, st, False, packing='binary'))

print("Case C: f=2,K=6,rho=0,G=2, earlier source, S^{-1}(S a) should equal a")
st = dict(x=1, y=16, t=0, b=0, u=0)
out = run(2, 6, 0, 2, st, False)
print("  a                ", st)
print("  S(a)             ", out)
print("  stepwise inverse ", run(2, 6, 0, 2, out, False, inverse=True))
print("  final-q inverse  ", run(2, 6, 0, 2, out, False, inverse=True, naive=True))

print("Case U: f=3,K=6,rho=0,G=2, later source, u_0 = B-1 = 3, x_{j_0}=1")
st = dict(x=1, y=1040, t=0, b=0, u=3)          # g_0=g_1=8 (guards pass), t digits 0
print("  input            ", st, "(bad as written: u_0 = B-1)")
print("  expected T(a)    ", ideal(3, 6, 0, st))
print("  actual S(a)      ", run(3, 6, 0, 2, st, True),
      "-> differs at bit j_1=6; the u clause of the bad set is necessary")
