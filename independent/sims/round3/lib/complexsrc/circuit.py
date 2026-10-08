"""Common circuit container and the outgoing-use / pivot role compiler.

A circuit is a DAG of additions over input triples.  Node supports are kept
as dicts {triple index: integer multiplicity} only for checking; additions
store (pivot child, second child).  Designated outputs are (node, target,
coefficient).  The role compiler follows the written rule shared by both PRs:
each outgoing edge of a node is a use; an input contributes one new role per
use; an addition reuses the role of its first (pivot) incoming edge for its
first outgoing use and allocates a new fanout role for every further use.
"""
from fractions import Fraction
from itertools import combinations


def triples(h):
    T = [sum(1 << p for p in c) for c in combinations(range(h), 3)]
    return T, {t: i for i, t in enumerate(T)}


class Circuit:
    def __init__(self, h):
        self.h = h
        self.T, self.tidx = triples(h)
        self.v = len(self.T)
        self.kind = []      # 'in' or 'add'
        self.args = []      # triple index, or (a, b)
        self.family = []    # free-form tag
        self.label = []     # label key (interpreted by the PR module)
        for i in range(self.v):
            self.kind.append('in')
            self.args.append(i)
            self.family.append('in')
            self.label.append(None)
        self.outputs = []   # (node, target triple index or tag, Fraction)

    def add(self, a, b, family, label=None):
        self.kind.append('add')
        self.args.append((a, b))
        self.family.append(family)
        self.label.append(label)
        return len(self.kind) - 1

    def n_nodes(self):
        return len(self.kind)

    # ------------------------------------------------------------------
    def prune(self, keep_extra=()):
        """Remove additions that feed no output (and no extra kept node)."""
        live = set(n for n, _, _ in self.outputs) | set(keep_extra)
        stack = list(live)
        while stack:
            z = stack.pop()
            if self.kind[z] == 'add':
                for c in self.args[z]:
                    if c not in live:
                        live.add(c)
                        stack.append(c)
        remap = {}
        kind, args, fam, lab = [], [], [], []
        for z in range(self.n_nodes()):
            if self.kind[z] == 'in' or z in live:
                remap[z] = len(kind)
                kind.append(self.kind[z])
                fam.append(self.family[z])
                lab.append(self.label[z])
                if self.kind[z] == 'add':
                    a, b = self.args[z]
                    args.append((remap[a], remap[b]))
                else:
                    args.append(self.args[z])
        self.kind, self.args, self.family, self.label = kind, args, fam, lab
        self.outputs = [(remap[n], t, c) for n, t, c in self.outputs]
        return remap

    def supports(self):
        """Exact integer multiplicity vector of every node over the inputs."""
        sup = []
        for z in range(self.n_nodes()):
            if self.kind[z] == 'in':
                sup.append({self.args[z]: 1})
            else:
                a, b = self.args[z]
                d = dict(sup[a])
                for k, m in sup[b].items():
                    d[k] = d.get(k, 0) + m
                sup.append(d)
        return sup

    def n_add(self):
        return sum(1 for k in self.kind if k == 'add')


class Roles:
    """Result of the role compiler."""

    def __init__(self, C):
        self.C = C
        n = C.n_nodes()
        uses = [[] for _ in range(n)]  # list of ('add', c, slot) or ('out', k)
        for z in range(n):
            if C.kind[z] == 'add':
                a, b = C.args[z]
                uses[a].append(('add', z, 0))
                uses[b].append(('add', z, 1))
        for k, (z, _, _) in enumerate(C.outputs):
            uses[z].append(('out', k))
        self.uses = uses
        nr = 0
        edge_role = {}   # (node, use index) -> role
        self.slot_roles = {}   # input triple -> roles
        self.gate = {}         # addition -> (pivot, second, fanout list)
        self.out_role = [None] * len(C.outputs)
        self.role_origin = []  # ('slot', T) or ('fan', z)
        for z in range(n):
            if C.kind[z] == 'in':
                rs = []
                for ui in range(len(uses[z])):
                    edge_role[(z, ui)] = nr
                    rs.append(nr)
                    self.role_origin.append(('slot', C.args[z]))
                    nr += 1
                self.slot_roles[C.args[z]] = rs
            else:
                a, b = C.args[z]
                ia = uses[a].index(('add', z, 0))
                ib = uses[b].index(('add', z, 1))
                piv = edge_role[(a, ia)]
                sec = edge_role[(b, ib)]
                assert len(uses[z]) >= 1, "unused addition"
                edge_role[(z, 0)] = piv
                fan = []
                for ui in range(1, len(uses[z])):
                    edge_role[(z, ui)] = nr
                    fan.append(nr)
                    self.role_origin.append(('fan', z))
                    nr += 1
                self.gate[z] = (piv, sec, fan)
            for ui, u in enumerate(uses[z]):
                if u[0] == 'out':
                    self.out_role[u[1]] = edge_role[(z, ui)]
        self.n_roles = nr
        self.order = [z for z in range(n) if C.kind[z] == 'add']

    # scalar semantics -------------------------------------------------
    def mix(self, vals, inverse=False):
        if not inverse:
            for z in self.order:
                p, s, fan = self.gate[z]
                vals[p] += vals[s]
                for f in fan:
                    vals[f] += vals[p]
        else:
            for z in reversed(self.order):
                p, s, fan = self.gate[z]
                for f in fan:
                    vals[f] -= vals[p]
                vals[p] -= vals[s]
