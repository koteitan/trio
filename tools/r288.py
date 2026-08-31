# -*- coding: utf-8 -*-
"""**(MEAS-A) —— 測度そのもの `towerMeas = 3|X| + rankDE` を `A != []` で測る。**

## ⚠ 定義（逐語）

    `rankDE d e = (if 0 < d then 1 else 0) + (if 0 < e then 1 else 0)`
    **`towerMeas X d e = 3 * |X| + rankDE d e`**
    `S = A ++ mTower Q d e n ++ block(Q,d,e,n).take (j+1)`、`last = |S|-1`、`i1 = srow S last`
    `c = parent S i1 last`、**`V = S[c:last]`**、
    **`d0 = if 0 < i1 then entry S 0 last − entry S 0 c else 0`**
    **`e0 = if 1 < i1 then entry S 1 last − entry S 1 c else 0`**
    ⟹ ★ 測るのは **`towerMeas V d0 e0 < towerMeas Q d e`**（`|V| < |Q|` ではありません）

## ⚠ 母集団を 1 行で

シート由来 `Q`（`psiI.json` の全接頭辞、重複除去、`hr0(Q)`）、**`A` を 8 通り**（深さを振る）、
`d`・`e`・`n`・`j`（`j = 0` を含む）を振る。**`(d = 0 → e = 0)` の有無で分けて**出す。
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

rank = lambda d, e: (1 if d > 0 else 0) + (1 if e > 0 else 0)
meas = lambda X, d, e: 3 * len(X) + rank(d, e)
AS = [[], [(0, 0, 0)], [(1, 0, 0)], [(2, 0, 0)], [(0, 1, 0)],
      [(0, 0, 0), (1, 0, 0)], [(1, 0, 0), (2, 1, 0)], [(3, 2, 1)]]


def run(Qs, DS, ES, NS, LQMAX, tag):
    c = Counter(); ex = []; t0 = time.time()
    for Q in Qs:
        if len(Q) > LQMAX or not hr0(Q): continue
        for A in AS:
            adep = ('A空' if not A else
                    ('A浅い' if min(q[0] for q in A) < Q[0][0] else
                     ('A同じ' if min(q[0] for q in A) == Q[0][0] else 'A深い')))
            for d in DS:
                for e in ES:
                    g2 = '★(d=0→e=0)真' if (d > 0 or e == 0) else '⛔(d=0→e=0)偽'
                    m0 = meas(Q, d, e)
                    for n in NS:
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        B = [tuple(x) for x in block(Q, d, e, n)]
                        for j in range(0, len(Q)):
                            S = [tuple(x) for x in A] + T + B[:j + 1]
                            last = len(S) - 1
                            i1 = srow(S, last)
                            cc = trio.parent(S, i1, last)
                            if cc is None: continue
                            V = [tuple(v) for v in S[cc:last]]
                            d0 = (S[last][0] - S[cc][0]) if i1 > 0 else 0
                            e0 = (S[last][1] - S[cc][1]) if i1 > 1 else 0
                            ok = meas(V, d0, e0) < m0
                            jg = 'j=0' if j == 0 else 'j>=1'
                            for key in (g2, adep, jg, f'n={n}', f'{g2}|{jg}'):
                                c[f'[{key}] 分母'] += 1
                                c[f'[{key}] ★減'] += 1 if ok else 0
                            c['総分母'] += 1
                            if ok: c['★ 総減'] += 1
                            elif len(ex) < 5:
                                ex.append((A, Q, d, e, n, j, cc, len(V), d0, e0,
                                           meas(V, d0, e0), m0))
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    d0t = c['総分母']
    print(f'  ★★ **総分母 {d0t}**   ★ **測度が減る** {c["★ 総減"]} '
          f'({100*c["★ 総減"]/max(d0t,1):8.4f}%)   ⛔ **減らない** {d0t - c["★ 総減"]}')
    for key in ['★(d=0→e=0)真', '⛔(d=0→e=0)偽', 'j=0', 'j>=1',
                '★(d=0→e=0)真|j=0', '★(d=0→e=0)真|j>=1',
                '⛔(d=0→e=0)偽|j=0', '⛔(d=0→e=0)偽|j>=1',
                'A空', 'A同じ', 'A深い', 'A浅い'] + [f'n={n}' for n in NS]:
        d = c[f'[{key}] 分母']
        if not d: continue
        ok = c[f'[{key}] ★減']
        m = ' ★★★ **100%**' if ok == d else f'  ⛔ **減らない {d-ok}**'
        print(f'      {key:22s} 分母 {d:8d}  ★ 減 {100*ok/max(d,1):8.4f}%{m}')
    for x in ex:
        print(f'      ⛔ 減らない例: A={x[0]} Q={x[1]} d={x[2]} e={x[3]} n={x[4]} j={x[5]} '
              f'c={x[6]} |V|={x[7]} d0={x[8]} e0={x[9]} meas {x[11]} → {x[10]}')
    print()


if __name__ == '__main__':
    run(sheetQ(6), (0, 1, 2), (0, 1, 2), (1, 2, 3, 5), 6,
        '★ シート由来 `hr0(Q)`（|Q|<=6）, d<=2, e<=2, n<=5, **A 8 通り**')
    run(sheetQ(8), (0, 1, 2, 3), (0, 1, 2), (1, 2, 3, 5, 8), 8,
        '★★ シート由来 `hr0(Q)`（|Q|<=8）, d<=3, e<=2, n<=8, **A 8 通り**')
