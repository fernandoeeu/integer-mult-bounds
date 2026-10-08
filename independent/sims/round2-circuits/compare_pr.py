"""Second, non-independent signal: compare our circuits with the PR's Python.

usage: python3 compare_pr.py pr6 CHECKOUT H
       python3 compare_pr.py pr4 CHECKOUT H
Compares node supports (as sets of triples), decompositions (unordered child
supports), designated outputs and role counts.
"""
import sys
import os
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
which, checkout, h = sys.argv[1], sys.argv[2], int(sys.argv[3])
sys.path.insert(0, os.path.join(checkout, 'scripts'))


def pr6():
    sys.path.insert(0, os.path.join(HERE, 'pr6'))
    from build import Builder
    import verify as V
    from bit_circuit import AlignedPairedCircuit
    theirs = AlignedPairedCircuit(h)
    code = theirs.compile()
    # export theirs in our graph format
    act = sorted(n for n in theirs.active if theirs.args[n])
    v = len(theirs.inputs)
    ren = {n: n - 1 for n in range(1, v + 1)}
    for k, n in enumerate(act):
        ren[n] = v + k
    left = [ren[theirs.args[n][0]] for n in act]
    right = [ren[theirs.args[n][1]] for n in act]
    partial = [(ren[n], i, T) for (i, T), n in sorted(theirs.outputs.items()) if T]
    center = [(ren[n], i) for (i, T), n in sorted(theirs.outputs.items()) if not T]
    gt = V.Graph(dict(h=h, v=v, left=left, right=right, partial=partial, center=center))
    go = V.Graph(Builder(h).graph())
    reps = []
    for G in (gt, go):
        cm, rep, conv, fails = V.supports(G)
        assert not fails
        dec = set()
        for k in range(G.c):
            dec.add((rep[G.v + k], frozenset((rep[G.left[k]], rep[G.right[k]]))))
        outs = {(i, tuple(T)): rep[n] for n, i, T in G.partial}
        cens = {i: rep[n] for n, i in G.center}
        reps.append((set(rep), dec, outs, cens, G.c))
    (st, dt, ot, ct, ct_), (so, do, oo, co, co_) = reps
    print('pr6 h', h, 'PR additions', ct_, 'ours', co_, 'PR roles', code['roles'],
          'ours c+q+h', co_ + len(oo) + len(co))
    print('  same node supports', st == so, 'only PR', len(st - so), 'only ours', len(so - st))
    print('  same decompositions', dt == do, 'only PR', len(dt - do), 'only ours', len(do - dt))
    print('  same outputs', ot == oo, 'same centers', ct == co)
    return st == so and ot == oo and ct == co


def pr4():
    sys.path.insert(0, os.path.join(HERE, 'pr4'))
    import pr4new
    from circuit import Roles
    from retained_complex import RetainedComplexCircuit
    theirs = RetainedComplexCircuit(h)
    T = [sum(1 << p for p in t) for t in theirs.inputs]
    sup = [0] + [1 << i for i in range(len(T))]
    for n in range(len(T) + 1, len(theirs.args)):
        a, b = theirs.args[n]
        sup.append(sup[a] | sup[b])

    def tset(bits, tri):
        out = []
        while bits:
            lb = bits & -bits
            bits ^= lb
            out.append(tri[lb.bit_length() - 1])
        return frozenset(out)
    st = {tset(sup[n], T) for n in theirs.active}
    dt = {(tset(sup[n], T), frozenset((tset(sup[theirs.args[n][0]], T), tset(sup[theirs.args[n][1]], T))))
          for n in theirs.active if theirs.args[n]}
    ot = {}
    for idx, node in theirs.outputs.items():
        if idx < len(theirs.targets):
            tgt, sign = theirs.targets[idx]
            key = (tgt, sign)
        else:
            key = ('tot', idx - len(theirs.targets))
        ot.setdefault(key, []).append(tset(sup[node], T))
    C = pr4new.build(h)
    R = Roles(C)
    ssup = C.supports()
    mine = []
    for z in range(C.n_nodes()):
        bits = [C.T[k] for k in ssup[z]]
        assert all(m == 1 for m in ssup[z].values())
        mine.append(frozenset(bits))
    so = set(mine)
    do = {(mine[z], frozenset((mine[C.args[z][0]], mine[C.args[z][1]])))
          for z in range(C.n_nodes()) if C.kind[z] == 'add'}
    oo = {}
    for z, t, c in C.outputs:
        if isinstance(t, tuple):
            i = t[1]
            key = ('tot', h - 2 + 1 if i == '*' else i)
            key = ('tot', (h - 1) if i == '*' else i)
        else:
            key = (C.T[t], 1 if c > 0 else -1)
        oo.setdefault(key, []).append(mine[z])
    norm = lambda d: {k: sorted(map(sorted, v)) for k, v in d.items()}
    print('pr4 h', h, 'PR additions', theirs.additions, 'ours', C.n_add(), 'PR roles', theirs.roles,
          'ours', R.n_roles, 'PR new ancestors', theirs.new_ancestors)
    print('  same node supports', st == so, 'only PR', len(st - so), 'only ours', len(so - st))
    print('  same decompositions', dt == do, 'only PR', len(dt - do), 'only ours', len(do - dt))
    print('  same outputs (target, sign, multiset of supports)', norm(ot) == norm(oo))
    pts = lambda S: sorted(set(p for t in S for p in range(h) if t >> p & 1))
    for x in sorted(st - so, key=len)[:3]:
        print('    only PR  : %d triples, union %s' % (len(x), pts(x)))
    for x in sorted(so - st, key=len)[:3]:
        print('    only ours: %d triples, union %s' % (len(x), pts(x)))
    return st == so and norm(ot) == norm(oo)


ok = pr6() if which == 'pr6' else pr4()
print('COMPARE', 'MATCH' if ok else 'DIFFER')
