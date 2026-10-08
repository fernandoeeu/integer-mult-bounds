"""PR 13 premise: in a stage-two invocation every auxiliary role's first gate
frame is D_0 and its last gate frame is D_1 (so source P_D0 gives a zero
entrance edge and exit I+P_D0-P_D1).  Uses round 3's schedule model of PR 7
(net.py, written from PR 7's note) on a concrete DAG.  Also reports stages 1
and 3 for contrast.  Usage: python3 stage2_ends.py h final.bin|mine"""
import sys, json
sys.path.insert(0, '../pr9chk')
import net
h = int(sys.argv[1])
g = net.mine(h) if sys.argv[2] == 'mine' else net.load_final(sys.argv[2], h)
sup, core, kinds, fails = net.check_structure(g)
assert not fails or h == 8, fails[:3]
R = net.Roles(g)
out = {}
for stage2 in (True, False):
    first, last = {}, {}
    for tag, wires, fr in net.schedule(g, R, kinds, stage2):
        for w in wires:
            if w[0] == 'r':
                first.setdefault(w[1], (fr, tag)); last[w[1]] = (fr, tag)
    roles = range(R.n)
    out['stage2' if stage2 else 'stage1/3'] = dict(
        roles=R.n, touched=len(first),
        first_D0=sum(1 for r in roles if r in first and first[r][0] == net.D0),
        last_D1=sum(1 for r in roles if r in last and last[r][0] == net.D1),
        first_tags=sorted({first[r][1] for r in first}), last_tags=sorted({last[r][1] for r in last}))
s2 = out['stage2']
out['PASS'] = s2['touched'] == s2['roles'] == s2['first_D0'] == s2['last_D1']
print(json.dumps(out))
