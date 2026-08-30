# -*- coding: utf-8 -*-
"""**R126 追加（z5）—— 「ブロック内で孤児」なら「塔全体でも孤児」か。**

**なぜ効くか**（先に書く。教訓 45）:
`Wset`/`Decrease:37` の **`oper_eq_pred_of_noParent`** は
「末尾列に親が無ければ `M⟦n⟧ = Pred M`（末尾を剥がすだけ）」と言う。

⟹ **もし `Q` が孤児のとき塔 `T = mTower Q d e n` の末尾列も塔全体で孤児なら、
`T⟦m⟧ = T.dropLast` になり、残差 B は「長さの帰納」だけで閉じる。**

**反例の形（先に書く）**: `Q` の末尾列はブロック内に親を持たないのに、
**前のブロックに親を見つける** `Q, d, e, n`。前のブロックは行0 が `d*k` だけ下、
行1 が `e*k` だけ下にあるので、**`d` や `e` が 0 なら同じ高さの列が前に並ぶ** ⟹
そこに親ができうる。⟹ **`d = 0` / `e = 0` が怪しい**。

**箱と単位**: 単位 = `(Q, d, e, n)`。`Q` は r126.py と同じ箱（根が狭義最浅・孤児のものだけ）。
`d, e ∈ {0,1,2}`、`n ∈ {2,3}`。**`W` 所属は判定しない**（明記）。
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r126 import srow, hasP
from r113 import Lift1, sh, mTower


def run(cm, L, DS, ES, NS):
    COL = [(d, b, c) for d in range(4) for b in range(3) for c in range(cm + 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for root in COL:
        tail = [x for x in COL if x[0] > root[0]]
        for t in itertools.product(tail, repeat=L - 1):
            Q = [root] + list(t)
            if hasP(Q):
                continue                       # 孤児だけ（残差 B の前提）
            for d in DS:
                for e in ES:
                    for n in NS:
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        j = len(T) - 1
                        orp = trio.parent(T, srow(T, j), j) is None
                        key = (('d=0' if d == 0 else 'd>=1'),
                               ('e=0' if e == 0 else 'e>=1'))
                        c[(key, 'ok 塔でも孤児' if orp else '**塔では親あり**')] += 1
                        c['全体 ok' if orp else '**全体 破れ**'] += 1
                        if not orp:
                            ex.setdefault(key, (Q, d, e, n,
                                                trio.parent(T, srow(T, j), j), len(T)))
    tot = c['全体 ok'] + c['**全体 破れ**']
    print(f'  行2<={cm} |Q|={L}: 分母 {tot:8d}  '
          f'**塔でも孤児 {c["全体 ok"]:8d} ({100*c["全体 ok"]/max(tot,1):6.2f}%)**  '
          f'**塔では親あり {c["**全体 破れ**"]:8d}**  [{time.time()-t0:.1f}s]')
    for k in sorted({k[0] for k in c if isinstance(k, tuple)}):
        o = c[(k, 'ok 塔でも孤児')]; b = c[(k, '**塔では親あり**')]
        print(f'      {k[0]:6s} {k[1]:6s}: 分母 {o+b:8d}  塔でも孤児 {o:8d} '
              f'({100*o/max(o+b,1):6.2f}%)  **破れ {b:8d}**')
    for k in sorted(ex):
        Q, d, e, n, p, ln = ex[k]
        print(f'      ★ 最小反例 {k}: Q={Q} d={d} e={e} n={n} → |T|={ln} '
              f'末尾列の親={p}（ブロック境界は {len(Q)} の倍数）')


if __name__ == '__main__':
    print('### R126c (z5) ブロック内で孤児 ⟹ 塔全体でも孤児 か')
    for cm in (1, 2):
        for L in (2, 3):
            run(cm, L, (0, 1, 2), (0, 1, 2), (2, 3))
