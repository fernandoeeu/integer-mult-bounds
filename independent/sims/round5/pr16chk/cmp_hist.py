"""Cross-check: PR 15's complex residual histogram (certificate) vs PR 16's note table
(3v^2 copies of local c_r + five classes).  Then PR 15's a_c with our own log bounds."""
import json, sys
from fractions import Fraction as Q
sys.argv = ['x']; exec(open('complex_arith.py').read().split('# complex moment')[0].replace("print('ALL PASS'", "#"))
d = json.load(open('pr15_complex.json'))['counts']['residual_histogram']
h15 = {int(k): v for k, v in d.items()}
same = h15 == Hh
print(('SAME ' if same else 'DISCREPANCY (informational, not a violation by itself) ') +
      'PR15 certificate histogram vs PR16 note histogram of the same h28 complex network',
      '' if same else {r: (h15.get(r), Hh.get(r), 'diff/N=%s' % Q(h15.get(r, 0) - Hh.get(r, 0), N)) for r in sorted(set(h15) | set(Hh)) if h15.get(r) != Hh.get(r)})
chk('PR15 histogram has the same rank sum s', sum(r*n for r, n in h15.items()) == s)
chk('PR15 histogram max rank 21896', max(h15) == 21896)
exec(open('complex_arith.py').read().split('# complex moment')[1].split("mo = moment")[0])
mo = moment(Q(4191487, 10**12)); chk('PR15 complex moment < 1 at 4191487e-12 (own logs)', mo < 1, float(1 - mo))
# Robustness: both savings under the OTHER PR's histogram (own log bounds)
Hsave = dict(Hh)
Hh.clear(); Hh.update(h15)
chk('PR15 hist: weights sum to 1-D/(Wm)', sum(Q(n*r, W*m) for r, n in Hh.items()) == 1 - Q(D, W*m))
mo = moment(Q(4191487, 10**12)); chk('PR15 hist: moment < 1 at PR15 a_c 4191487e-12 (own logs)', mo < 1, float(1 - mo))
mo = moment(Q(4, 10**6)); chk('PR15 hist: moment < 1 at PR16 a_c 4e-6', mo < 1, float(1 - mo))
Hh.clear(); Hh.update(Hsave)
print('ALL PASS (robustness)' if ok else 'SOME FAIL (see above)')
