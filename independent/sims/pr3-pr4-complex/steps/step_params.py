import sys
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src'))
from params import *
from fractions import Fraction as Q
c3=pr3_counts(25,108195); print('PR3',c3)
print('  claimed W 1741801270000 L 10315500000 s 27215641140750000 eta 28/205789375:',
      c3['W']==1741801270000, c3['L']==10315500000, c3['s']==27215641140750000, c3['eta']==Q(28,205789375))
print('  log m < 966/100:', log_upper_ok(15625,Q(966,100)), ' eta > 14e-9*9.66:', c3['eta']>Q(14,10**9)*Q(966,100))
c4=pr4_counts(24,365760); print('PR4',c4)
print('  claimed W 3013310215168 L 6796219584 s 41655997423981952 eta 365/5084246016:',
      c4['W']==3013310215168, c4['L']==6796219584, c4['s']==41655997423981952, c4['eta']==Q(365,5084246016))
print('  log m < 477/50:', log_upper_ok(13824,Q(477,50)), ' eta > 750e-11*477/50:', c4['eta']>Q(750,10**11)*Q(477,50),
      'margin', c4['eta']-Q(750,10**11)*Q(477,50))
c4u=pr4_counts(24,365760,shared=False); print('PR4 without stage sharing eta',c4u['eta'],float(c4u['eta']), ' supports 1-sigma up to ~', float(c4u['eta']/Q(477,50)))
tau=1-Q(296,10**11)
print('PR3 recurrence', recurrence(tau,1-Q(14,10**9),Q(1,1000),Q(999,1000),1-Q(2958,10**12),1-Q(2956,10**12)))
print('PR4 recurrence', recurrence(tau,1-Q(750,10**11),Q(1,1000),Q(1),1-Q(2959,10**12),1-Q(2958,10**12)))
print('head recurrence', recurrence(tau,1-Q(418,10**12),Q(1,1000),Q(1,5),1-Q(1671,4*10**12),1-Q(167,4*10**11)))
