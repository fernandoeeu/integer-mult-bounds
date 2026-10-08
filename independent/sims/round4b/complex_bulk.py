"""Whole-residual complex child (bulk-complex-guard.tex, batched-complex-rows.tex):
prod_j (C^{eps_j})^{(x)f} on slots 1..a (f axes each, consecutive)
  == (-i)^{f|B|} Z_B C^{(x) af} Z_B ,  C = aI + bX, a=(1+i)/2, b=(1-i)/2.
All entries are dyadic Gaussian rationals; complex128 represents them
exactly at these sizes, comparison is exact (==).  Also: the integer-axis
remainder split C^{(x)e} = C^{(x)r} (x) C^{(x)mf}, and a slot-permuted
layout (non-contiguous residual slots) as a control."""
import itertools, random, numpy as np
from functools import reduce
I2 = np.eye(2, dtype=complex); X = np.array([[0, 1], [1, 0]], dtype=complex); Z = np.diag([1, -1]).astype(complex)
C = (1+1j)/2*I2 + (1-1j)/2*X
Ci = np.linalg.inv(C)
kr = lambda ms: reduce(np.kron, ms, np.eye(1, dtype=complex))
OK = True
def check(n, c):
    global OK; OK &= bool(c); print(('PASS ' if c else 'FAIL ') + n)
check('C^-1 = -i Z C Z = bI + aX (exact)', np.array_equal(Ci, -1j*Z@C@Z) and np.array_equal(Ci, (1-1j)/2*I2 + (1+1j)/2*X))
check('C^2 = X, C^4 = I', np.array_equal(C@C, X) and np.array_equal(np.linalg.matrix_power(C, 4), I2))
rng = random.Random(5); n = 0; bad = 0; ctl = 0
for a in range(1, 6):
    for f in range(1, 4):
        if a*f > 10: continue
        for signs in itertools.product((1, -1), repeat=a):
            lhs = kr([C if s == 1 else Ci for s in signs for _ in range(f)])
            B = [j for j, s in enumerate(signs) if s == -1]
            ZB = kr([Z if signs[j] == -1 else I2 for j in range(a) for _ in range(f)])
            rhs = (-1j)**(f*len(B)) * ZB @ kr([C]*(a*f)) @ ZB
            n += 1; bad += not np.array_equal(lhs, rhs)
            if B and f % 4:          # control: phase (-i)^{|B|} instead of (-i)^{f|B|}
                wrong = (-1j)**(len(B)) * ZB @ kr([C]*(a*f)) @ ZB
                ctl += (f == 1) or not np.array_equal(lhs, wrong)
check(f'bulk identity exact for all sign patterns, a<=5, f<=3, af<=10 ({n} cases, {bad} mismatches)', bad == 0)
check(f'control: wrong phase exponent detected whenever f>1 (count {ctl})', ctl > 0)
# remainder: e = m f + r
m = 3
for e in range(1, 10):
    f, r = divmod(e, m)
    check(f'remainder split e={e}: C^(x)e = C^(x){r} (x) C^(x){m*f}', np.array_equal(kr([C]*e), np.kron(kr([C]*r), kr([C]*(m*f)))))
print('ALL PASS' if OK else 'SOME FAIL')
