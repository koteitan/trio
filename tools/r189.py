# -*- coding: utf-8 -*-
"""★★★ (u2b) 決着 —— **`hr0 ∧ hz0` の下でランクは必ず真に減る**か。

r188: (M1)(M4) の破れが 0.54 → 0.84 → 1.73 → 2.69%（箱を広げるほど増える）。
**破れ例は全部 `entry Q 2 0 > 0`（＝ `hz0` を破る）。**
⟹ **`hr0 ∧ hz0` を課して測り直す。陽性対照 = 課さない版（r188、鳴っている）。**

**⚠ 見積もり: 課せば 100%（破れ 0）。破れたら (u2b) の機構は誤り。**
"""
import sys, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block
from r171 import step_det
from r183 import hr0, hnb, hz0


def rank(d, e): return (1 if d > 0 else 0) + (1 if e > 0 else 0)


def run(E, LS, NS, DE, nsamp, seed, force, tag):
    COL = [(a, b, c) for a in range(E) for b in range(E) for c in (0, 1)]
    rnd = random.Random(seed); c = Counter(); ex = []
    for _ in range(nsamp):
        L = rnd.choice(LS)
        if force:                       # `hr0 ∧ hz0` を構成的に（`hnb` は放置）
            a = rnd.randrange(E - 1)
            Q = [(a, rnd.randrange(E), 0)] + \
                [(rnd.randrange(a + 1, E), rnd.randrange(E), rnd.randrange(2))
                 for _ in range(L - 1)]
            assert hr0(Q) and hz0(Q)
        else:
            root = rnd.choice(COL); hi = [x for x in COL if x[0] > root[0]]
            if not hi: continue
            Q = [root] + [rnd.choice(hi) for _ in range(L - 1)]
        d, e = rnd.choice(DE), rnd.choice(DE)
        for n in NS:
            for j in range(L):
                T = [tuple(x) for x in mTower(Q, d, e, n)]
                S = T + block(Q, d, e, n)[:j + 1]
                last = len(S) - 1
                i1 = srow(S, last)
                if trio.parent(S, i1, last) is None: continue
                V, d2, e2 = step_det(Q, d, e, n, j)
                c['段'] += 1
                if len(V) >= L:
                    c['★ 非減少の段'] += 1
                    c[('非減少の srow', i1)] += 1
                    if i1 <= 1: c['  (M1) srow <= 1'] += 1
                    else:
                        c['  ⚠ (M1) 破れ'] += 1
                        if len(ex) < 4: ex.append(('M1', Q, d, e, n, j, i1, len(V)))
                    if rank(d2, e2) < rank(d, e): c['  ★ (M4) ランクが真に減った'] += 1
                    else:
                        c['  ⚠⚠ (M4) 破れ'] += 1
                        if len(ex) < 8: ex.append(('M4', Q, d, e, n, j, i1, (d2, e2)))
                    if (d, e) == (0, 0): c['  ⚠ (M3) 破れ (0,0) から非減少'] += 1
                    if not hnb(Q): c['  ★ うち hnb を満たさない'] += 1
    nd = c['★ 非減少の段']
    print(f'### {tag} 値域<{E} |Q|∈{LS} n∈{tuple(NS)} (d,e)∈{tuple(DE)}  '
          f'段 {c["段"]}  非減少 {nd}')
    print('    非減少の srow: ', dict(sorted((k[1], c[k]) for k in c
                                     if isinstance(k, tuple))))
    for k in sorted(x for x in c if isinstance(x, str) and x.startswith('  ')):
        print(f'    {k:38s} {c[k]:8d} ({100*c[k]/max(nd,1):7.3f}%)')
    for x in ex: print('      ⚠ 破れ例', x)
    print()


if __name__ == '__main__':
    print('#### ★ 本命: `hr0 ∧ hz0` を構成的に満たす `Q`（`hnb` は放置）')
    run(6, (3,4,5,6,8), (1,2,3,4,5), range(6),  20000, 171, True,  '本命')
    run(9, (4,6,8,10),  (1,2,3,4,6), range(9),  12000, 173, True,  '本命・広い箱')
    run(12,(5,8,12),    (1,2,3,5,8), range(12),  8000, 175, True,  '本命・さらに広い箱')
    print('#### 陽性対照: 前提を課さない（r188 と同じ。鳴るべき）')
    run(9, (4,6,8,10),  (1,2,3,4,6), range(9),  12000, 173, False, '陽性対照')
