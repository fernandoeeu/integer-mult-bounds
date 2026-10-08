"""Compare our independently built merged graph with the PR's Python graph
(scripts/aligned_paired_network.circuit) node by node, via an additive 64-bit
support hash (supports of an addition are disjoint unions, so hash = sum).
Usage: python3 compare_pr.py <pr-checkout> <our-export.json> [h]
"""
import json, random, sys
from collections import Counter
from itertools import combinations

pr, ours = sys.argv[1], sys.argv[2]
h = int(sys.argv[3]) if len(sys.argv) > 3 else 50
sys.path.insert(0, pr + '/scripts')
from aligned_paired_network import circuit  # noqa: E402

M = (1 << 64) - 1
rng = random.Random(20261008)
triples = list(combinations(range(h), 3))
tid = {t: k for k, t in enumerate(triples)}
r = [rng.getrandbits(64) for _ in triples]

c = circuit(h)
H = {}
for node in sorted(c.active):
    if c.args[node] is None:
        H[node] = r[node - 1]
    else:
        a, b = c.args[node]
        H[node] = (H[a] + H[b]) & M
pr_add = Counter((H[n], tuple(sorted((H[c.args[n][0]], H[c.args[n][1]])))) for n in c.active if c.args[n])
pr_out = {(i, tid[t]): H[n] for (i, t), n in c.outputs.items()}
pr_nodes = set(H[n] for n in c.active if c.args[n])
print(f'PR: additions={sum(pr_add.values())} distinct_add_supports={len(pr_nodes)} outputs={len(pr_out)} merged={c.merged}')
del c

g = json.load(open(ours))
T = len(triples)
G = r + [0] * len(g['left'])
for k, (a, b) in enumerate(zip(g['left'], g['right'])):
    G[T + k] = (G[a] + G[b]) & M
our_add = Counter((G[T + k], tuple(sorted((G[a], G[b])))) for k, (a, b) in enumerate(zip(g['left'], g['right'])))
our_out = {(i, t): G[n] for n, i, t in zip(g['outNode'], g['outCommon'], g['outTarget'])}
print(f'ours: additions={sum(our_add.values())} outputs={len(our_out)}')
print('same set of node supports:', set(G[T:]) == pr_nodes)
print('same decompositions (multiset of node, unordered children):', our_add == pr_add)
print('decompositions only in ours:', sum((our_add - pr_add).values()), ' only in PR:', sum((pr_add - our_add).values()))
print('same outputs (common, target) -> support:', our_out == pr_out)
