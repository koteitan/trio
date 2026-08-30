# -*- coding: utf-8 -*-
"""**(J0) —— `j = 0` の手の構造。**

## ⚠ 母集団と定義（1 行ずつ）

シート由来 `Q`（`psiI.json` の全接頭辞、重複除去、**`hr0(Q)`**）＋ 接頭辞 `A`（8 通り）、
`d`・`e`・`n` を振り、**`j = 0`** に限る。
`S = A ++ mTower Q d e n ++ [ブロックの根]`、`last = |S|-1`、`i1 = srow S last`、
`c = parent S i1 last`、**`V = S[c:last]`**、
`d0 = if 0<i1 then entry S 0 last − entry S 0 c else 0`、
`e0 = if 1<i1 then entry S 1 last − entry S 1 c else 0`。
**`towerMeas X a b = 3|X| + rankDE a b`**。

## 測るもの

    (a) **`c = |A| + (n−1)|Q|`（前のブロックの根）か**
    (b) **`(d0, e0) = (d, e)` か** ／ **`towerMeas` の 減 / 同 / 増**
    (c) **`n = 1` のとき**
    (d) **破れる手と破れない手の違い**
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block
from r206 import hr0
from r284 import sheetQ
from r288 import rank, meas, AS


def run(Qs, DS, ES, NS, LQMAX, tag, U=0):
    c = Counter(); ex = []; t0 = time.time()
    for Q0 in Qs:
        if len(Q0) > LQMAX or not hr0(Q0): continue
        Q = [(x + U, y, z) for x, y, z in Q0]
        LQ = len(Q)
        for A in AS:
            for d in DS:
                for e in ES:
                    m0 = meas(Q, d, e)
                    for n in NS:
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        B = [tuple(x) for x in block(Q, d, e, n)]
                        S = [tuple(x) for x in A] + T + B[:1]     # ★ j = 0
                        last = len(S) - 1
                        i1 = srow(S, last)
                        cc = trio.parent(S, i1, last)
                        if cc is None: continue
                        V = [tuple(v) for v in S[cc:last]]
                        d0 = (S[last][0] - S[cc][0]) if i1 > 0 else 0
                        e0 = (S[last][1] - S[cc][1]) if i1 > 1 else 0
                        m1 = meas(V, d0, e0)
                        k = '減' if m1 < m0 else ('同' if m1 == m0 else '増')
                        c['★ 分母（j=0）'] += 1
                        c[f'towerMeas {k}'] += 1
                        g = '★減る手' if k == '減' else '⛔ 減らない手'
                        c[f'[{g}] 分母'] += 1
                        # (a)
                        prev = len(A) + (n - 1) * LQ
                        c[f'[{g}] (a) c = 前のブロックの根 ? {cc == prev}'] += 1
                        c[f'[{g}] (a) c が A の中 ? {cc < len(A)}'] += 1
                        # (b)
                        c[f'[{g}] (b) (d0,e0)=(d,e) ? {(d0, e0) == (d, e)}'] += 1
                        c[f'[{g}] (b) |V| vs |Q|: '
                          f'{"<" if len(V) < LQ else ("=" if len(V) == LQ else ">")}'] += 1
                        # (c)
                        c[f'[{g}] (c) n={min(n,3)}'] += 1
                        c[f'[{g}] (d) srow={i1}'] += 1
                        if k != '減' and len(ex) < 4:
                            ex.append((A, Q, d, e, n, cc, prev, len(V), LQ, d0, e0, m0, m1))
    d = c['★ 分母（j=0）']
    print(f'### {tag}  [{time.time()-t0:.1f}s]  ★ **分母（j=0）{d}**')
    print(f'  ★★ **towerMeas**: 減 {c["towerMeas 減"]} ({100*c["towerMeas 減"]/max(d,1):8.4f}%)  '
          f'⛔ **同** {c["towerMeas 同"]} ({100*c["towerMeas 同"]/max(d,1):8.4f}%)  '
          f'⛔ **増** {c["towerMeas 増"]} ({100*c["towerMeas 増"]/max(d,1):8.4f}%)')
    for g in ('⛔ 減らない手', '★減る手'):
        dd = c[f'[{g}] 分母']
        if not dd: continue
        print(f'  **{g}**: 分母 {dd}')
        for kk in sorted(c):
            if kk.startswith(f'[{g}] ('):
                print(f'      {kk[len(g)+3:]:34s} {c[kk]:8d} ({100*c[kk]/dd:8.4f}%)')
    for x in ex:
        print(f'      ⛔ 減らない例: A={x[0]} Q={x[1]} d={x[2]} e={x[3]} n={x[4]} '
              f'c={x[5]}（前のブロックの根={x[6]}）|V|={x[7]} |Q|={x[8]} '
              f'(d0,e0)=({x[9]},{x[10]}) meas {x[11]}→{x[12]}')
    print()


if __name__ == '__main__':
    run(sheetQ(8), (0, 1, 2, 3), (0, 1, 2), (1, 2, 3, 5, 8), 8,
        '★ シート由来 `hr0(Q)`（|Q|<=8）, A 8 通り, j=0（`u=0`）')
    run(sheetQ(6), (0, 1, 2), (0, 1, 2), (1, 2, 3, 5), 6,
        '★★ 同上 ＋ **`Q` の行 0 を +2**（`A` を浅くする）', U=2)
