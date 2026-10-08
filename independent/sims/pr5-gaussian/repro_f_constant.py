"""Minimal reproduction of a constant slip in Lemma chirped-gaussian, map E
(notes/fast-gaussian-resampling.tex, PR 5 @ d3d370c):

  "The inputs f_j are formed by Lemma 2.14 ... for 2^{-ceil(1.14 a^2)} e^{pi a^2 beta_j^2},
   a shift, and one product with u_j; their errors are at most 2^{4-P} F."
  "Then F = e^{pi a^2/4} < 2^{1.14 a^2} <= 2^{1.14 p}"

An approximation z~ allowed by the quoted interface (|z~ - z| <= 2^{1-P}) becomes, after the
shift by K = ceil(1.14 a^2), an error up to 2^{K+1-P}, which exceeds 2^{4-P} e^{pi a^2/4}
once K + 1 > 4 + (pi/(4 ln 2)) a^2, first possible at a = 21 (p > 441); shown here at a = 22, p = 485.
Harmless: with F := 2^K the bound holds and P = 34p still satisfies
P >= p + Gamma + ceil(log2(F L_A)) + 11 (checked in t1_exact.py [5]); final errors stay < 1
(t4 grid). Two derivations below: (A) closed form, (B) an explicit computation.
"""
from fractions import Fraction as Fr
from flint import arb, fmpq, ctx

p, al, s, t, j = 485, 22, 4, 5, 2
P = 34 * p
ctx.prec = P + 200
a2 = al * al
K = -(-114 * a2 // 100)
q = (2 * t * j + s) // (2 * s); beta = Fr(t * j, s) - q
assert beta * beta == Fr(1, 4)               # f_j attains F = e^{pi a^2/4}
F = (arb.pi() * a2 / 4).exp()
# (A) closed form in bits
print("K =", K, " log2 F =", (F.log() / arb(2).log()).str(10))
print("(A) worst shifted error / claimed bound = 2^(K+1-4-log2 F) =", (arb(2) ** (K - 3) / F).str(10))
# (B) explicit: z~ = ceil(z 2^P) + 1  (error in [1,2) units 2^-P, allowed), u_j = 1 exactly
z = (arb.pi() * a2 * arb(fmpq(beta.numerator ** 2, beta.denominator ** 2))).exp() / arb(2) ** K
r = int((z * arb(2) ** P).upper().ceil().unique_fmpz()) + 1
assert (z * arb(2) ** P - r).abs_upper() <= 2
u = 1 << p                                     # u_j = 1 in D_p
f_num = ((u << (P - p)) * (r << K) + (1 << (P - 1))) >> P   # shift, product, round to precision P
f_true = F                                     # e^{pi a^2 beta^2} * 1
err = abs(arb(f_num) / arb(2) ** P - f_true)
claim = arb(2) ** (4 - P) * F
print("(B) actual error / claimed 2^(4-P)F =", (err / claim).str(10))
print("expected: > 1 (claim violated)  actual:", "VIOLATED" if err > claim else "holds")
print("with repaired F = 2^K:", "holds" if err <= arb(2) ** (4 - P + K) else "VIOLATED")
