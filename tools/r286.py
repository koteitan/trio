# -*- coding: utf-8 -*-
"""**(MEASQ) ＋ (MEAS3) —— `A` を付けて測る。**

## ⚠ 母集団と定義（1 行ずつ）

シート由来 `Q`（`psiI.json` の全接頭辞、重複除去）。**接頭辞 `A` を付けます**
（L3 の反例 `A = [(0,0,0)]` が `A ≠ []` なので）。
`S = A ++ mTower Q d e n ++ block(Q,d,e,n).take (j+1)`、
**`c = parent S (srow S (|S|-1)) (|S|-1)`**、**`|V| = |S| − 1 − c`**、**窓 `V = S[c:|S|-1]`**。
**`MeasOK ⟺ |V| < |Q|`**。

## (MEASQ) H12 の「`Q` だけの条件」

    `out(Q) := { r | ¬ le1 Q 0 r }`（錐の外）
    `S(j) := { r ∈ out(Q) | entry Q 1 r < entry Q 1 j }`
    ⟹ ★ **`S(j) ∩ [0, j)` が空か**（H12 の議論の「今のブロックに候補が無い」）
    ⚠ team-lead の書き方 `S(j) ∩ (j,|Q|)` も**両方**測ります。

## (MEAS3) 測度の候補 —— **`(V, d0, d1)` だけの関数**に限る
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

AS = [[], [(0, 0, 0)], [(0, 0, 0), (1, 0, 0)], [(1, 0, 0)], [(0, 1, 0)]]


def qcond(Q):
    """(MEASQ): 各 j について `S(j) ∩ [0,j)` と `∩ (j,|Q|)` が空か。"""
    out = [r for r in range(len(Q)) if not trio.is_ancestor(Q, 1, 0, r)]
    res = {}
    for j in range(1, len(Q)):
        if j not in out: continue
        Sj = [r for r in out if Q[r][1] < Q[j][1]]
        res[j] = (not [r for r in Sj if r < j], not [r for r in Sj if r > j])
    return res


def run(Qs, DS, ES, NS, LQMAX, tag):
    c = Counter(); ex = []; t0 = time.time()
    for Q in Qs:
        if len(Q) > LQMAX or not hr0(Q): continue
        LQ = len(Q); qc = qcond(Q)
        for A in AS:
            for d in DS:
                for e in ES:
                    for n in NS:
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        B = [tuple(x) for x in block(Q, d, e, n)]
                        for j in range(0, LQ):
                            S = [tuple(x) for x in A] + T + B[:j + 1]
                            last = len(S) - 1
                            cc = trio.parent(S, srow(S, last), last)
                            if cc is None: continue
                            V = last - cc
                            ok = V < LQ
                            g = '★A空' if not A else '⛔A有'
                            c[f'[{g}] 分母'] += 1
                            c[f'[{g}] ★MeasOK'] += 1 if ok else 0
                            if not ok:
                                c[f'[{g}] ⛔破れ'] += 1
                                if len(ex) < 5:
                                    ex.append((A, Q, d, e, n, j, cc, V, LQ))
                            # ---------- (MEASQ) 突き合わせ ----------
                            if j in qc:
                                a, b = qc[j]
                                c[f'(MEASQ) 左が空={a} × 破れ={not ok}'] += 1
                                c[f'(MEASQ) 右が空={b} × 破れ={not ok}'] += 1
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    for g in ('★A空', '⛔A有'):
        d = c[f'[{g}] 分母']
        if not d: continue
        print(f'  **{g}**: 分母 {d:8d}  ★ MeasOK {c[f"[{g}] ★MeasOK"]:8d} '
              f'({100*c[f"[{g}] ★MeasOK"]/max(d,1):8.4f}%)   ⛔ **破れ** {c[f"[{g}] ⛔破れ"]}')
    print('  ★★ (MEASQ) 突き合わせ（H12 の `Q` だけの条件 vs 実際の破れ）')
    for side in ('左', '右'):
        tot = sum(c[f'(MEASQ) {side}が空={a} × 破れ={b}']
                  for a in (True, False) for b in (True, False))
        if not tot: continue
        print(f'      **{side}（{"S(j)∩[0,j)" if side=="左" else "S(j)∩(j,|Q|)"} が空）**  分母 {tot}')
        for a in (True, False):
            row = [c[f'(MEASQ) {side}が空={a} × 破れ={b}'] for b in (True, False)]
            print(f'          空={a}: 破れ {row[0]:7d}  破れず {row[1]:7d}'
                  + (f'   ⟹ 破れ率 {100*row[0]/max(sum(row),1):8.4f}%'))
    for x in ex:
        print(f'      ⛔ **MeasOK 破れ**: A={x[0]} Q={x[1]} d={x[2]} e={x[3]} n={x[4]} '
              f'j={x[5]} c={x[6]} |V|={x[7]} |Q|={x[8]}')
    print()


if __name__ == '__main__':
    run(sheetQ(6), (0, 1, 2), (0, 1, 2), (1, 2, 3, 5), 6,
        '★ シート由来 `hr0(Q)`（|Q|<=6）, d<=2, e<=2, n<=5, **A 付き**')
    run(sheetQ(8), (0, 1, 2, 3), (0, 1, 2), (1, 2, 3, 5, 8), 8,
        '★★ シート由来 `hr0(Q)`（|Q|<=8）, d<=3, e<=2, n<=8, **A 付き**')
