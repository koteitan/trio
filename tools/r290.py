# -*- coding: utf-8 -*-
"""**(MEAS-B) —— `A` を含む量で、両方の手で減るものを探す。**

## ⚠ 固定運用（team-lead 指示）

**`entry Q 0 0 > 0` の `Q` を必ず混ぜる**（`Q` の行 0 を `u` 持ち上げる）。
**群ごとの分母を先に報告**する。

## ⚠ 状態と手（1 行）

状態 ＝ **`(A, Q, d, e)`**。`S = A ++ mTower Q d e n ++ block.take (j+1)`、`last = |S|-1`、
`i1 = srow S last`、`c = parent S i1 last` ⟹ **次の状態 `(A' = S[:c], V = S[c:last], d0, e0)`**。
`d0 = if 0<i1 then entry S 0 last − entry S 0 c else 0`、
`e0 = if 1<i1 then entry S 1 last − entry S 1 c else 0`。

## 候補（`A` を含む量）

    (1) **`lev`**: `lev X j = 2*entry X 1 j + entry X 2 j` の 根 / 最大 / 総和
    (2) `|A| + |V|`
    (3) **`A` の中の「`Q` の根より浅い列」の数**
    (4) **浅さのギャップ** `entry Q 0 0 − min(A の行 0)`（`A` 空なら 0）
    (5) **`A` の最小の行 0**
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block
from r206 import hr0
from r284 import sheetQ
from r288 import rank, meas

lev = lambda q: 2 * q[1] + q[2]
AS = [[], [(0, 0, 0)], [(0, 1, 0)], [(1, 0, 0)], [(0, 0, 0), (1, 0, 0)],
      [(0, 2, 1)], [(1, 0, 0), (2, 1, 0)], [(0, 0, 1)]]


def feats(A, Q, d, e):
    amin0 = min((q[0] for q in A), default=Q[0][0])
    return {
        '(1a) lev(Q の根)': lev(Q[0]),
        '(1b) lev の最大（A++Q）': max(lev(q) for q in list(A) + list(Q)),
        '(1c) lev の総和（A++Q）': sum(lev(q) for q in list(A) + list(Q)),
        '(2) |A| + |Q|': len(A) + len(Q),
        '(3) A の浅い列の数': sum(1 for q in A if q[0] < Q[0][0]),
        '(4) 浅さのギャップ': max(0, Q[0][0] - amin0),
        '(5) A の最小の行 0': amin0,
        '(参考) towerMeas': meas(Q, d, e),
        'LEX (lev根, towerMeas)': (lev(Q[0]), meas(Q, d, e)),
        'LEX (浅い列数, towerMeas)': (sum(1 for q in A if q[0] < Q[0][0]), meas(Q, d, e)),
    }


def run(Qs, US, DS, ES, NS, LQMAX, tag):
    c = Counter(); keys = None; t0 = time.time()
    for Q0 in Qs:
        if len(Q0) > LQMAX or not hr0(Q0): continue
        for u in US:
            Q = [(x + u, y, z) for x, y, z in Q0]
            for A in AS:
                shallow = any(q[0] < Q[0][0] for q in A)
                f = feats(A, Q, 0, 0)
                if keys is None: keys = list(f)
                for d in DS:
                    for e in ES:
                        f = feats(A, Q, d, e)
                        for n in NS:
                            T = [tuple(x) for x in mTower(Q, d, e, n)]
                            B = [tuple(x) for x in block(Q, d, e, n)]
                            for j in range(0, len(Q)):
                                S = [tuple(x) for x in A] + T + B[:j + 1]
                                last = len(S) - 1
                                i1 = srow(S, last)
                                cc = trio.parent(S, i1, last)
                                if cc is None: continue
                                A2 = [tuple(v) for v in S[:cc]]
                                V = [tuple(v) for v in S[cc:last]]
                                if not V: continue
                                d0 = (S[last][0] - S[cc][0]) if i1 > 0 else 0
                                e0 = (S[last][1] - S[cc][1]) if i1 > 1 else 0
                                g = feats(A2, V, d0, e0)
                                grp = '⛔ A が浅い' if shallow else '★ A が浅くない'
                                c[f'{grp} 分母'] += 1
                                for k in keys:
                                    a, b = f[k], g[k]
                                    c[f'{grp}|{k}|' + ('減' if b < a else
                                                       ('同' if b == a else '増'))] += 1
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    for grp in ('⛔ A が浅い', '★ A が浅くない'):
        d = c[f'{grp} 分母']
        print(f'  **{grp}**: 分母 {d}')
        if not d: continue
        for k in keys:
            dec, sm, inc = (c[f'{grp}|{k}|減'], c[f'{grp}|{k}|同'], c[f'{grp}|{k}|増'])
            m = ' ★★★ **非増加**' if inc == 0 else ''
            print(f'      {k:30s} 減 {100*dec/max(d,1):7.3f}%  同 {100*sm/max(d,1):7.3f}%  '
                  f'増 {100*inc/max(d,1):7.3f}%{m}')
    print()


if __name__ == '__main__':
    run(sheetQ(6), (0, 1, 2), (0, 1, 2), (0, 1, 2), (1, 2, 3), 6,
        '★★ シート由来 `hr0(Q)`（|Q|<=6）, **u∈{0,1,2}（entry Q 0 0 > 0 を混ぜる）**, A 8 通り')
