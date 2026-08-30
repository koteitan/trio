# -*- coding: utf-8 -*-
"""(u1e) ★ **`hnb` は落とせるか** —— 分母を上げて決める。

r185: `hr0 ∧ hz0` で `j>=1` の非減少が **0 / 21,127**（`hnb` なし）。分母が小さい。
**`hr0 ∧ hz0` を構成的に満たし、`hnb` は満たさない `Q`** を作って分母を 10^5 級にする。

**陽性対照**: `hr0` だけ / `hz0` だけ ⟹ 鳴るはず（r185 で 0.098〜4.54%）。
"""
import sys, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
from collections import Counter
from r183 import hr0, hnb, hz0, probe


def gen(rnd, E, L, mode):
    """mode: 'r0z0' = hr0∧hz0 を構成的に（hnb は放置）
             'r0'   = hr0 のみ（hz0 は放置）  'z0' = hz0 のみ"""
    if mode == 'r0z0':
        a = rnd.randrange(E - 1)
        return [(a, rnd.randrange(E), 0)] + \
               [(rnd.randrange(a + 1, E), rnd.randrange(E), rnd.randrange(2))
                for _ in range(L - 1)]
    if mode == 'r0':
        a = rnd.randrange(E - 1)
        return [(a, rnd.randrange(E), rnd.randrange(2))] + \
               [(rnd.randrange(a + 1, E), rnd.randrange(E), rnd.randrange(2))
                for _ in range(L - 1)]
    return [(rnd.randrange(E), rnd.randrange(E), 0)] + \
           [(rnd.randrange(E), rnd.randrange(E), rnd.randrange(2)) for _ in range(L - 1)]


def run(E, LS, NS, DE, nsamp, seed, mode, tag):
    rnd = random.Random(seed); c = Counter(); ex = []
    for _ in range(nsamp):
        L = rnd.choice(LS)
        Q = gen(rnd, E, L, mode)
        assert (mode != 'r0z0') or (hr0(Q) and hz0(Q))
        d, e, n = rnd.choice(DE), rnd.choice(DE), rnd.choice(NS)
        for j in range(1, L):
            r = probe(Q, d, e, n, j)
            if r is None: continue
            lv, par, inblk = r
            c['段(j>=1)'] += 1
            if hnb(Q): c['  うち hnb も満たす'] += 1
            else: c['  ★ hnb を満たさない'] += 1
            if lv >= L:
                c['⚠ 非減少 |V|>=|Q|'] += 1
                if not hnb(Q):
                    c['⚠★ hnb なしで非減少'] += 1
                    if len(ex) < 4: ex.append((Q, d, e, n, j, lv))
            if not inblk:
                c['親がブロックの外'] += 1
                if not hnb(Q): c['  ★ hnb なしで親がブロックの外'] += 1
    t = c['段(j>=1)']
    print(f'### {tag} 値域<{E} |Q|∈{LS} n∈{tuple(NS)} (d,e)∈{tuple(DE)}  段 {t}')
    for k in ['  うち hnb も満たす', '  ★ hnb を満たさない', '⚠ 非減少 |V|>=|Q|',
              '⚠★ hnb なしで非減少', '親がブロックの外', '  ★ hnb なしで親がブロックの外']:
        print(f'    {k:34s} {c[k]:8d} ({100*c[k]/max(t,1):7.4f}%)')
    for x in ex: print(f'      ⚠ 反例 Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} |V|={x[5]}')
    print()


if __name__ == '__main__':
    for (E, LS, NS, DE, n) in [(6, (3,4,5,6,8), (2,3,4,5), range(6), 40000),
                               (9, (4,6,8,10),  (2,3,4,5), range(9), 30000),
                               (12,(5,8,12),    (2,3,4,6), range(12), 20000)]:
        run(E, LS, NS, DE, n, 151, 'r0z0', '★ 本命 `hr0∧hz0` を構成（`hnb` は放置）')
    print('#### 陽性対照（鳴るべき）')
    run(6, (3,4,5,6,8), (2,3,4,5), range(6), 40000, 153, 'r0', '陽性対照 `hr0` だけ')
    run(6, (3,4,5,6,8), (2,3,4,5), range(6), 40000, 155, 'z0', '陽性対照 `hz0` だけ')
