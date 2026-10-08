"""PR 7 complex bank sharing (stage-1 bank (A,B) = stage-3 bank (B, pi(A)),
pi = flip every point to its partner): combinatorics at h = 8..28 and the
joining edge E -> H as actual subspaces of F_2^{h^3} (sampled pairs, h = 8)."""
import sys, os, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'complexsrc'))
import sharing
for h in (8, 10, 12, 20, 28):
    print('h', h, sharing.combinatorics(h))
random.seed(7)
T, pi = sharing.pi_list(8)
pairs = [(random.randrange(len(T)), random.randrange(len(T))) for _ in range(12)] + [(0, 0), (5, 5)]
res = sharing.join_check(8, pairs)
print('h 8 join E subset H, residual dim m-2h, nondegenerate, nonalternating, onb:',
      all(r[2] and r[3] for r in res), len(res), 'pairs')
