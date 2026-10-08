"""Own star-template synthesis for PR 9, written from its README only:

  "PR #7's greedy rule prioritizes the most frequent pair of current terms,
   then the smallest union support. The new rule instead favors the largest
   union support when the frequency is tied. The driver compares the published
   rule and two versions of this alternative, with ascending and descending
   union masks. It prunes unused addition ancestors, verifies each candidate,
   and retains the smallest circuit for each canonical template."

Unstated by the README (fixed here, documented): final tie break on the pair
itself (lexicographic on (a, b) with a < b); a pair whose union already exists
is selected but costs nothing; terms are partitions and every term containing a
sub-partition of the chosen union collapses to it.  The published PR 7 rule is
taken from PR 7's optimize() (inherited, already reviewed in round 3).

Input: demands.txt (core old m1 m2 ...) as written by PR 7's C++ pass.
Canonical order (README of PR 7 / verify_dag.cpp): intact global pairs first,
then partners of removed points.  Output: templates.bin in the verify_dag
format, header h.  Prints counts as JSON.
Usage: python3 mytemplates.py H demands.txt out.bin [--mode select|large|large_rev|published|mine_only]
"""
import os, sys, json, struct
from collections import Counter
from itertools import combinations
_PR9 = os.environ.get('PR9_CHECKOUT', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'pr9'))  # git archive of PR 9 head cfd6a2b
sys.path[:0] = [os.path.join(_PR9, 'research/prime-field-followup/vendor'), os.path.join(_PR9, 'scripts')]
from prime_field_circuit import optimize as pr7_optimize   # inherited rule only


def canon(h, core, masks):
    order = [x for x in range(h) if not core >> x & 1 and not core >> (x ^ 1) & 1]
    order += [x for x in range(h) if not core >> x & 1 and core >> (x ^ 1) & 1]
    assert len(order) == h - 4
    out = []
    for m in masks:
        z = 0
        for j, x in enumerate(order):
            if m >> x & 1:
                z |= 1 << j
        assert bin(z).count('1') == bin(m).count('1')
        out.append(z)
    return tuple(sorted(set(out)))


def greedy_large(targets, desc):
    """Most frequent pair; ties: LARGER union popcount; then union mask
    ascending (desc=False) or descending (desc=True); then pair."""
    terms = []
    for t in targets:
        terms.append(frozenset(1 << i for i in range(t.bit_length()) if t >> i & 1))
    terms = [set(t) for t in terms]
    have = set(x for t in terms for x in t)
    gates = []
    while any(len(t) > 1 for t in terms):
        freq = Counter()
        for t in terms:
            s = sorted(t)
            for i in range(len(s)):
                for j in range(i + 1, len(s)):
                    freq[(s[i], s[j])] += 1
        def key(p):
            u = p[0] | p[1]
            return (-freq[p], -bin(u).count('1'), -u if desc else u, p)
        a, b = min(freq, key=key)
        u = a | b
        if u not in have:
            have.add(u)
            gates.append((a, b))
        for t in terms:
            inside = [x for x in t if x & ~u == 0]
            if len(inside) > 1 and sum(inside) == u:
                for x in inside:
                    t.discard(x)
                t.add(u)
    assert sorted(next(iter(t)) for t in terms) == sorted(targets)
    return prune(targets, gates)


def prune(targets, gates):
    par = {a | b: (a, b) for a, b in gates}
    need, st = set(), list(targets)
    while st:
        x = st.pop()
        if x in need:
            continue
        need.add(x)
        st.extend(par.get(x, ()))
    return [g for g in gates if (g[0] | g[1]) in need]


def check(targets, gates):
    n = max(targets).bit_length()
    have = {1 << i for i in range(n)}
    for a, b in gates:
        assert a and b and not a & b and a in have and b in have and (a | b) not in have
        have.add(a | b)
    assert all(t in have for t in targets)


def main():
    h, dem, out = int(sys.argv[1]), sys.argv[2], sys.argv[3]
    mode = sys.argv[sys.argv.index('--mode') + 1] if '--mode' in sys.argv else 'select'
    mult = Counter()
    for line in open(dem):
        core, old, *masks = map(int, line.split())
        mult[canon(h, core, masks)] += 1
    chosen, pub_total, sel_total, differs, winners = {}, 0, 0, 0, Counter()
    for tg, k in sorted(mult.items()):
        tl = list(tg)
        cands = {}
        if mode in ('select', 'published'):
            cands['published'] = pr7_optimize(tl)
        if mode in ('select', 'large', 'mine_only'):
            cands['large'] = greedy_large(tl, False)
        if mode in ('select', 'large_rev', 'mine_only'):
            cands['large_rev'] = greedy_large(tl, True)
        for g in cands.values():
            check(tl, g)
        best = min(cands, key=lambda nm: len(cands[nm]))
        chosen[tg] = cands[best]
        winners[best] += k
        if 'published' in cands:
            pub_total += k * len(cands['published'])
            if len(cands[best]) < len(cands['published']):
                differs += 1
        sel_total += k * len(cands[best])
    with open(out, 'wb') as f:
        w = lambda *xs: f.write(struct.pack('<' + 'I' * len(xs), *xs))
        w(h, len(chosen))
        for tg, gates in sorted(chosen.items()):
            w(len(tg), len(gates), *tg)
            for a, b in gates:
                w(a, b)
    print(json.dumps(dict(h=h, mode=mode, stars=sum(mult.values()), templates=len(mult),
                          published_star_additions=pub_total, selected_star_additions=sel_total,
                          saved=pub_total - sel_total if pub_total else None,
                          templates_improved=differs, winners_weighted=dict(winners))))


if __name__ == '__main__':
    main()
