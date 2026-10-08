"""Driver: runs t4_blocks.run over a parameter grid; one line per config."""
import sys, time
from collections import Counter
from fractions import Fraction as Fr
import t4_blocks as T

GRID = [
    # p, alpha, s, t, maps
    (101, 2, 4, 5, 'S,E'),
    (101, 3, 9, 10, 'S,E'), (101, 3, 4, 5, 'S,E'), (101, 3, 7, 8, 'S,E'), (101, 3, 37, 46, 'S,E'),
    (101, 5, 25, 26, 'S,E'), (101, 5, 4, 5, 'S,E'), (101, 5, 50, 57, 'S,E'),
    (101, 10, 100, 101, 'S,E'), (101, 10, 4, 5, 'S,E'), (101, 10, 37, 46, 'S,E'), (101, 10, 63, 71, 'S,E'),
    (110, 10, 41, 51, 'S,E'),
    (121, 10, 100, 101, 'S,E'), (121, 10, 4, 5, 'S,E'),
    (122, 11, 121, 122, 'S,E'), (122, 11, 4, 5, 'S,E'), (122, 11, 41, 51, 'S,E'), (122, 2, 4, 5, 'S,E'),
    (150, 12, 144, 145, 'S,E'), (150, 12, 4, 5, 'S,E'), (150, 7, 49, 50, 'S,E'),
    (256, 15, 225, 226, 'S,E'), (256, 15, 4, 5, 'S,E'), (256, 15, 97, 121, 'S,E'), (256, 2, 4, 5, 'S,E'),
    (500, 22, 4, 5, 'S,E'), (500, 22, 97, 121, 'S,E'), (500, 21, 4, 5, 'S,E'), (500, 3, 9, 10, 'S,E'),
    (500, 22, 484, 485, 'E'),
    (1000, 31, 4, 5, 'S,E'), (1000, 31, 961, 962, 'E'), (1000, 10, 100, 101, 'E'),
]
sel = sys.argv[1] if len(sys.argv) > 1 else 'all'
tot = Counter(); nfail_cfg = 0
for (p, al, s, t, maps) in GRID:
    if sel == 'part1' and p > 300: continue
    if sel == 'part2' and p != 500: continue
    if sel == 'part3' and not (p == 1000 and s <= 100): continue
    if sel == 'part4' and not (p == 1000 and s > 100): continue
    ims = ['ones', 'rand', 'rim', 'alt']; ams = ['near', 'up', 'down', 'rand']
    if p == 1000 and s > 100:
        ims = ['ones', 'rand']; ams = ['near', 'up']
    t0 = time.time()
    r = T.run(p, al, s, t, ims, ams, maps=maps.split(','))
    kinds = Counter(f.split(' j=')[0].split(' a=')[0].split(' k=')[0].split(' l=')[0].split(' b=')[0] for f in r['fails'])
    tot.update(kinds)
    worstS = max((v['final'] for v in r['S'].values()), default=None)
    worstSB = max((v['finalB'] for v in r['S'].values()), default=None)
    worstE = max((v['final'] for v in r['E'].values()), default=None)
    worstF = max((v['f_over_claim'] for v in r['E'].values()), default=None)
    print(f"p={p} a={al} s={s} t={t} th={Fr(t-s,s)} maps={maps} checks={r['checks']} "
          f"maxerr S'={worstS} (single-round {worstSB}) E={worstE} [units 2^-p]; f_err/claim={worstF}; "
          f"fails={dict(kinds)} ({time.time()-t0:.0f}s)", flush=True)
print("TOTAL failing check kinds:", dict(tot))
