# -*- coding: utf-8 -*-
"""**(HR0-HERED) —— 次の窓 `V` は `hr0(V)` を満たすか。**

## ⚠ 母集団と定義（1 行ずつ）

`psiI.json` の DBMS 列の全接頭辞 `Q`（重複除去、`entry Q 2 0 = 0`）、`d`・`e`・`n` を振る。
`S = mTower Q d e n ++ block(Q,d,e,n).take (j+1)`、**`c = parent S (srow S (|S|-1)) (|S|-1)`**、
**窓 `V = S[c:|S|-1]`**（末尾列を含まない）。
**`hr0(V) :⟺ ∀ l, 0 < l < |V| → entry V 0 0 < entry V 0 l`**。

## ⚠ team-lead の読みへの注意（私の予測）

`nextrel0` の最小性から `hr0(V)` が出るのは **`srow(S, last) = 0` のとき**だけのはずです。
⟹ ★ **`srow >= 1` では親は行 1 / 行 2 の親**なので、**行 0 の最小性は使えません**。
⟹ ⟹ ★★ ですから **`srow` で分けて測ります**。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
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
        h = hr0(Q)
        for d in DS:
            for e in ES:
                for n in NS:
                    T = [tuple(x) for x in mTower(Q, d, e, n)]
                    B = [tuple(x) for x in block(Q, d, e, n)]
                    for j in range(1, len(Q)):
                        S = T + B[:j + 1]
                        last = len(S) - 1
                        sr = srow(S, last)
                        cc = trio.parent(S, sr, last)
                        if cc is None: continue
                        V = [tuple(v) for v in S[cc:last]]
                        if len(V) < 2: continue
                        g = '★hr0(Q)真' if h else '⛔hr0(Q)偽'
                        ok = hr0(V)
                        c[f'[{g}] 分母'] += 1
                        c[f'[{g}] ★hr0(V)'] += 1 if ok else 0
                        c[f'[{g}][srow={sr}] 分母'] += 1
                        c[f'[{g}][srow={sr}] ★hr0(V)'] += 1 if ok else 0
                        if not ok and len(ex) < 6:
                            ex.append((Q, d, e, n, j, cc, sr, V, h))
    print(f'### {tag}  Q {len(Qs)} 個  [{time.time()-t0:.1f}s]')
    for g in ('★hr0(Q)真', '⛔hr0(Q)偽'):
        for suf in ('', '[srow=0]', '[srow=1]', '[srow=2]'):
            key = f'[{g}]{suf}'
            d = c[f'{key} 分母']
            if not d: continue
            ok = c[f'{key} ★hr0(V)']
            m = ' ★★★ **100%**' if ok == d else (' ⛔ **破れあり**' if ok < d else '')
            print(f'  {key:24s} 分母 {d:8d}  ★ **hr0(V)** {ok:8d} '
                  f'({100*ok/max(d,1):8.4f}%)   ⛔ 破れ {d-ok}{m}')
    for x in ex:
        print(f'      ⛔ hr0(V) が破れる例: Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} '
              f'c={x[5]} srow={x[6]} hr0(Q)={x[8]}')
        print(f'          V={x[7]}')
    print()


if __name__ == '__main__':
    run(5, (1, 2), (0, 1), (1, 2), '⛔ 小さい箱（|Q|<=5, d<=2, e<=1, n<=2）')
    run(8, (1, 2, 3), (0, 1, 2), (1, 2, 3, 5), '★ |Q|<=8, d<=3, e<=2, n<=5')
    run(10, (1, 2, 3, 4), (0, 1, 2, 3), (1, 2, 3, 5, 8), '★★ |Q|<=10, d<=4, e<=3, n<=8')
