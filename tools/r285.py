# -*- coding: utf-8 -*-
"""**(MEASOK) ＋ (R2-N) —— `MeasOK` を `d = 0` と大きい `n` で叩く。**

## ⚠ 母集団と定義（1 行ずつ）

★ シート由来: `psiI.json` の DBMS 列の全接頭辞 `Q`（重複除去）で **`hr0(Q)`** を満たすもの。
`S = mTower Q d e n ++ block(Q,d,e,n).take (j+1)`、
**`c = parent S (srow S (|S|-1)) (|S|-1)`**、**`|V| = |S| − 1 − c`**。
**`MeasOK` ⟺ `|V| < |Q|`**。

## ⚠ §R258 との違い

    ⛔ §R258 は **`d ∈ {1,2,3,4}`** で **`d = 0` を入れていませんでした**
    ⛔ §R258 は **`n <= 8`** まで
    ⟹ ★ ここでは **`d = 0` を入れ**、**`n` を 30 まで**伸ばします（H12 の予測の検証）。
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


def run(Qs, DS, ES, NS, LQMAX, tag):
    c = Counter(); ex = []; t0 = time.time()
    for Q in Qs:
        if len(Q) > LQMAX or not hr0(Q): continue
        LQ = len(Q)
        for d in DS:
            for e in ES:
                for n in NS:
                    T = [tuple(x) for x in mTower(Q, d, e, n)]
                    B = [tuple(x) for x in block(Q, d, e, n)]
                    for j in range(1, LQ):
                        S = T + B[:j + 1]
                        last = len(S) - 1
                        sr = srow(S, last)
                        cc = trio.parent(S, sr, last)
                        if cc is None: continue
                        V = last - cc
                        ok = V < LQ
                        cone = trio.is_ancestor(S, 1, 0, last)
                        c['★ 分母'] += 1
                        c[f'   n={n} 分母'] += 1
                        c[f'   d={d} 分母'] += 1
                        c[f'   e={e} 分母'] += 1
                        c[f'   srow={sr} 分母'] += 1
                        c['   的が錐の中 分母' if cone else '   ★的が錐の外 分母'] += 1
                        if ok:
                            c['★ MeasOK'] += 1
                            c[f'   n={n} ok'] += 1; c[f'   d={d} ok'] += 1
                            c[f'   e={e} ok'] += 1; c[f'   srow={sr} ok'] += 1
                            c['   的が錐の中 ok' if cone else '   ★的が錐の外 ok'] += 1
                        else:
                            c['⛔ **MeasOK 破れ**'] += 1
                            if len(ex) < 6:
                                ex.append((Q, d, e, n, j, cc, V, LQ, sr, cone))
    d0 = c['★ 分母']
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    print(f'  ★★ **分母 {d0}**   ★ **MeasOK** {c["★ MeasOK"]} '
          f'({100*c["★ MeasOK"]/max(d0,1):8.4f}%)   '
          f'⛔ **破れ {c["⛔ **MeasOK 破れ**"]}**')
    for pre in ('   n=', '   d=', '   e=', '   srow=', '   的が', '   ★的が'):
        ks = sorted({k[:-3] for k in c if k.startswith(pre) and k.endswith(' 分母')},
                    key=lambda s: (len(s), s))
        for k in ks:
            dd = c[k + ' 分母']; oo = c[k + ' ok']
            if not dd: continue
            m = '' if oo == dd else '  ⛔ **破れ %d**' % (dd - oo)
            print(f'      {k.strip():14s} 分母 {dd:8d}  MeasOK {100*oo/max(dd,1):8.4f}%{m}')
    for x in ex:
        print(f'      ⛔ **MeasOK 破れ**: Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} '
              f'c={x[5]} |V|={x[6]} |Q|={x[7]} srow={x[8]} 錐の中={x[9]}')
    print()


if __name__ == '__main__':
    Q8 = sheetQ(8)
    run(Q8, (0, 1, 2), (0, 1, 2), (1, 2, 3, 5, 8, 13, 20, 30), 8,
        '★★★ シート由来 `hr0(Q)`（|Q|<=8）, **d∈{0,1,2}**, e<=2, **n<=30**')
    run(sheetQ(10), (0, 1, 2, 3, 4), (0, 1, 2, 3), (1, 2, 3, 5, 8, 13, 20), 10,
        '★★★★ シート由来 `hr0(Q)`（|Q|<=10）, **d<=4**, e<=3, **n<=20**')
