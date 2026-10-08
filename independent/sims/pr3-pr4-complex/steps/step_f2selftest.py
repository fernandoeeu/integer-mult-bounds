import sys, os, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src'))
from f2 import *
random.seed(1)
def span(vs):
    out={0}
    for v in vs: out|={x^v for x in out}
    return out
h=7; allv=range(1<<h); n=0
for _ in range(400):
    gens=[random.randrange(1,1<<h) for _ in range(random.randint(0,5))]
    U=Space(h,gens); su=span(gens)
    assert all(U.contains(x)==(x in su) for x in allv)
    assert span(perp(U).basis())=={x for x in allv if all(dot(x,u)==0 for u in su)}
    big=gens+[random.randrange(1,1<<h) for _ in range(2)]; V=Space(h,big); sv=span(big)
    assert span(residual(U,V).basis())=={x for x in sv if all(dot(x,u)==0 for u in su)}
    nd=all(any(dot(x,y) for y in su) for x in su if x); assert nondegenerate(U)==nd
    na=any(norm(x) for x in su); assert nonalternating(U)==na
    B=orthonormal_basis(U)
    if U.dim()==0: assert B==[]
    elif nd and na: assert check_orthonormal(B,U)
    else: assert B is None
    n+=1
print('f2 algebra agrees with brute-force enumeration on',n,'random subspaces of F_2^7')
