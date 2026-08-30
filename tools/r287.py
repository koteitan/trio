# -*- coding: utf-8 -*-
"""**(MEAS3) —— `(V, d0, d1)` だけの関数で、両方の手で減るものを探す。**

## ⚠ 母集団と定義（1 行ずつ）

シート由来 `Q`（`hr0(Q)`）＋ 接頭辞 `A`。`S = A ++ mTower Q d e n ++ block.take (j+1)`、
`c = parent S (srow S (|S|-1)) (|S|-1)`、**窓 `V = S[c:|S|-1]`**、
**`d0' = if 0 < i1 then entry S 0 last − entry S 0 c else 0`**、
**`e0' = if 1 < i1 then entry S 1 last − entry S 1 c else 0`**（`Trio.lean:106-114` 逐語）。
**手の分類**: ★ `c >= |A| + |mTower|`（ブロックの中）／ ⛔ それ以外（塔・接頭辞へ）。

⚠ **`A` を含む量は候補に入れません**（L3 の制約）。**`d = 0` を必ず含めます**。
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
from r286 import AS


def feats(V, d0, d1):
    out = sum(1 for r in range(len(V)) if not trio.is_ancestor(V, 1, 0, r))
    return {
        '|V|': len(V),
        '★ entry V 0 0': V[0][0],
        'entry V 1 0': V[0][1],
        'd0': d0,
        'd0 + d1': d0 + d1,
        '|V| + d0': len(V) + d0,
        '|V| + d0 + d1': len(V) + d0 + d1,
        '|V| * (d0+1)': len(V) * (d0 + 1),
        'V の錐の外の列数': out,
        'LEX (entry V 0 0, |V|)': (V[0][0], len(V)),
        'LEX (|V|, entry V 0 0)': (len(V), V[0][0]),
        'LEX (|V|, d0, d1)': (len(V), d0, d1),
    }


def run(Qs, DS, ES, NS, LQMAX, tag):
    c = Counter(); keys = None; t0 = time.time()
    for Q in Qs:
        if len(Q) > LQMAX or not hr0(Q): continue
        for A in AS:
            for d in DS:
                for e in ES:
                    f = feats([tuple(x) for x in Q], d, e)
                    if keys is None: keys = list(f)
                    for n in NS:
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        B = [tuple(x) for x in block(Q, d, e, n)]
                        bs = len(A) + len(T)
                        for j in range(1, len(Q)):
                            S = [tuple(x) for x in A] + T + B[:j + 1]
                            last = len(S) - 1
                            i1 = srow(S, last)
                            cc = trio.parent(S, i1, last)
                            if cc is None or last - cc < 1: continue
                            V = [tuple(v) for v in S[cc:last]]
                            d0 = (S[last][0] - S[cc][0]) if i1 > 0 else 0
                            e0 = (S[last][1] - S[cc][1]) if i1 > 1 else 0
                            g = feats(V, d0, e0)
                            grp = '★ ブロックの中' if cc >= bs else '⛔ 塔・接頭辞へ'
                            c[f'{grp} 分母'] += 1
                            for k in keys:
                                a, b = f[k], g[k]
                                c[f'{grp}|{k}|' + ('減' if b < a else
                                                   ('同' if b == a else '増'))] += 1
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    for grp in ('⛔ 塔・接頭辞へ', '★ ブロックの中'):
        d = c[f'{grp} 分母']
        print(f'  **{grp}**: 分母 {d}')
        for k in keys:
            dec, sm, inc = (c[f'{grp}|{k}|減'], c[f'{grp}|{k}|同'], c[f'{grp}|{k}|増'])
            m = (' ★★★ **非増加**' if inc == 0 and d else '')
            print(f'      {k:26s} 減 {100*dec/max(d,1):7.3f}%  同 {100*sm/max(d,1):7.3f}%  '
                  f'増 {100*inc/max(d,1):7.3f}%{m}')
    print()


if __name__ == '__main__':
    run(sheetQ(8), (0, 1, 2, 3), (0, 1, 2), (1, 2, 3, 5), 8,
        '★★ シート由来 `hr0(Q)`（|Q|<=8）, **d<=3（d=0 込み）**, e<=2, n<=5, A 付き')
