# -*- coding: utf-8 -*-
"""(SNOC) の違反が **maxlen を上げても生き残るか**。生き残ればそれは本物の候補。"""
import sys, time, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
import wfix, inw2
COLS = [(x, b, c) for x in range(3) for b in range(x + 1)
        for c in range(min(b, 1) + 1)]
seeds = [list(C) for L in (1, 2, 3) for C in itertools.product(COLS, repeat=L)]
u = int(sys.argv[1]) if len(sys.argv) > 1 else 0
keep = None
print('**u=%d で maxlen を上げる。違反する対の集合の推移**' % u, flush=True)
for ml in (5, 6, 7, 8, 9, 10, 11, 12):
    t0 = time.time()
    w = wfix.Wfix(u, maxlen=ml)
    w.seed(seeds)
    if w.cap:
        print('   maxlen=%d **打切り**（宇宙が大きすぎる。ここまで）' % ml, flush=True)
        break
    V = set()
    for C in seeds:
        if len(C) >= ml or not w.mem(C):
            continue
        for p in COLS:
            S = C + [p]
            if not inw2.has_parent(S, len(C)):
                continue
            if not w.mem(S):
                V.add((tuple(map(tuple, C)), p))
    keep = V if keep is None else (keep & V)
    print('   maxlen=%-3d 節点 %7d |W| %6d  違反 %5d  **生き残り %5d**  (%.0fs)'
          % (ml, len(w.nodes), len(w.X), len(V), len(keep), time.time() - t0),
          flush=True)
    if not keep:
        break
print(flush=True)
if keep:
    print('**生き残った対（違反の候補）%d 件:**' % len(keep))
    for C, p in sorted(keep, key=lambda t: (len(t[0]), t))[:6]:
        print('   C=%s  p=%s' % (list(C), p))
else:
    print('**生き残りゼロ ⟹ (SNOC) に反例なし（maxlen を上げると全部つぶれる）。**')
