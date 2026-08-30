# -*- coding: utf-8 -*-
"""**(WIN-LEN) ＋ (AMIN-281)。**

## ⚠ L3 の定義を逐語で

    `S = mTower Q d e n ++ block(Q,d,e,n).take (j+1)`（`T` に相当）
    **`c = parent S (srow S (|S|-1)) (|S|-1)`**、**`|V| = |S| − 1 − c`**
    **越境 ＝ `c < |mTower Q d e n|`**（親が最後のブロックの外／塔・接頭辞）
    ⟹ ★ **新しい残差 ＝ `|V| < |Q|`**

## ⚠ 母集団を 1 行で

`psiI.json` の DBMS 列の全接頭辞 `Q`（重複除去、`entry Q 2 0 = 0`）で `|Q| <= LQ`。
`d`・`e`・`n` を振る。**`hr0(Q)` の有無で分けて**出す（§R257 の発見）。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block
from r265 import qs
from r206 import hr0


def run(LQ, DS, ES, NS, tag):
    c = Counter(); ex = []; t0 = time.time()
    Qs = qs(LQ)
    for Q in Qs:
        h = hr0(Q); LQn = len(Q)
        for d in DS:
            for e in ES:
                for n in NS:
                    T = [tuple(x) for x in mTower(Q, d, e, n)]
                    B = [tuple(x) for x in block(Q, d, e, n)]
                    br = len(T)
                    for j in range(1, LQn):
                        S = T + B[:j + 1]
                        last = len(S) - 1
                        cc = trio.parent(S, srow(S, last), last)
                        if cc is None: continue
                        V = last - cc
                        cross = cc < br
                        g = '★hr0真' if h else '⛔hr0偽'
                        k = '減' if V < LQn else ('同' if V == LQn else '増')
                        c[f'[{g}] 分母'] += 1
                        c[f'[{g}]|{k}'] += 1
                        gg = '⛔越境' if cross else '★ブロック内'
                        c[f'[{g}][{gg}] 分母'] += 1
                        c[f'[{g}][{gg}]|{k}'] += 1
                        if k != '減' and len(ex) < 6:
                            ex.append((Q, d, e, n, j, cc, br, V, LQn, h, cross))
    print(f'### {tag}  Q {len(Qs)} 個  [{time.time()-t0:.1f}s]')
    for g in ('★hr0真', '⛔hr0偽'):
        for gg in ('', '★ブロック内', '⛔越境'):
            key = f'[{g}]' + (f'[{gg}]' if gg else '')
            d = c[f'{key} 分母']
            if not d: continue
            dec, sm, inc = c[f'{key}|減'], c[f'{key}|同'], c[f'{key}|増']
            m = ' ★★★ **|V| < |Q| が 100%**' if sm == 0 and inc == 0 else ''
            print(f'  {key:22s} 分母 {d:8d}  ★ **|V|<|Q|** {100*dec/max(d,1):8.4f}%  '
                  f'⛔ 同 {100*sm/max(d,1):8.4f}%  ⛔ 増 {100*inc/max(d,1):8.4f}%{m}')
    for x in ex:
        print(f'      ⛔ |V| >= |Q| の例: Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} '
              f'c={x[5]} 塔長={x[6]} |V|={x[7]} |Q|={x[8]} hr0={x[9]} 越境={x[10]}')
    print()


if __name__ == '__main__':
    run(5, (1, 2), (0, 1), (1, 2), '⛔ L3 の箱に近い（|Q|<=5, d<=2, e<=1, n<=2）')
    run(8, (1, 2, 3), (0, 1, 2), (1, 2, 3, 5), '★ |Q|<=8, d<=3, e<=2, n<=5')
    run(10, (1, 2, 3, 4), (0, 1, 2, 3), (1, 2, 3, 5, 8), '★★ |Q|<=10, d<=4, e<=3, n<=8')
