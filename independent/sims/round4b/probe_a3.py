import random
from lin import *
from family import instances, controlled_S
rng = random.Random(2)
inst, G = instances(3, rng, n_each=1)
A3 = next(A for k, A, c in inst if k == 'A3')
m = 27; a = rank(A3); r = m - a
good = 0
for s in range(6):
    S, Si = controlled_S(3, random.Random(100+s))
    P = mul(mul(S, A3), Si)
    good += det_nonzero([row[m-r:] for row in P[:r]])
print('A3 instance from seed 2: corner invertible for', good, '/ 6 fresh controlled S draws')
