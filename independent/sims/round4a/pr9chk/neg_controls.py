"""PR 9 negative controls: corrupted star templates must be rejected by the
independent verifier (verify_dag) and the full network check (net.py)."""
import struct, subprocess, sys, json
h = 10; src = 'w10/sel.bin'
w = list(struct.unpack('<%dI' % (len(open(src,'rb').read()) // 4), open(src,'rb').read()))
def write(words, path):
    open(path, 'wb').write(struct.pack('<%dI' % len(words), *words))
# locate first template with >=2 gates
p = 2; nt = w[1]
for t in range(nt):
    nout, ng = w[p], w[p+1]
    if ng >= 2: break
    p += 2 + nout + 2*ng
gpos = p + 2 + nout
res = {}
def verdict(name, words):
    write(words, 'w10/neg.bin')
    r = subprocess.run(['./verify_dag', str(h), 'w10/dag.bin', 'w10/neg.bin'], capture_output=True, text=True)
    res[name] = 'rejected' if r.returncode != 0 else 'NOT REJECTED'
# 1 overlapping gate: second operand := first operand | its own bits
x = list(w); a, b = x[gpos], x[gpos+1]; x[gpos+1] = b | a; verdict('overlapping_gate', x)
# 2 drop the last gate of that template (a target becomes uncomputed)
x = list(w[:gpos + 2*(ng-1)]) + w[gpos + 2*ng:]; x[p+1] = ng - 1; verdict('dropped_gate', x)
# 3 target mask changed (template no longer matches star demand)
x = list(w); x[p+2] ^= 1 << 5; verdict('changed_target', x)
print(json.dumps(res))
sys.exit(0 if all(v == 'rejected' for v in res.values()) else 1)
