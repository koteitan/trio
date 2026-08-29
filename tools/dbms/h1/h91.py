# -*- coding: utf-8 -*-
"""**(e) 第 3 の枝: 錐の外なのに `Q` の中で行 2 の親を持つ列。**

§255 で (C2)（錐の外 ∧ `Q` で孤児）は閉じた。残るのは

    **錐の外（`¬ le1 Q 0 j`）だが、根以外の祖先から行 2 の親を持つ列**（実測 0.7%）

これは `snocStep_outOfCone` の `horph` を満たさない。⟹ **射程外。**

⚠ ところが L3 の (C1)（錐の中）の要点は「錐の中」ではなく
**「親が同じブロックの中にいる ⟹ 窓 < |Q| ⟹ §138 の測度」**のはず。
⟹ **測るべきは「錐の中か」ではなく「親が同じブロックか」。**

    (e1) 塔の中で親を持つとき、その親は**同じブロック**か、**前のブロック**か
    (e2) ＝ **復活（前のブロックから親が来る）は本当に起きるか**
    (e3) `n` と `|R|` を振る（教訓 21）

**復活ゼロなら**: 枝は「親なし（(C2)、無料）」と「親は同じブロック（(C1) の測度）」の
2 つだけになり、**第 3 の枝は消える**。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import fmt, entry, srow, has_parent, dom_m, argOK, Lift1, shiftr01
from h88 import mTower, le1
from collections import Counter

ref = wref.Ref(maxnodes=4000)


def run(cmax, lens, ns=(1, 2, 3), tmax=2, vmax=3):
    cols = [(a, b, c) for a in range(1, 3) for b in range(3) for c in range(cmax)]
    print('### 箱: 行2 < %d、`v<%d`、`t<%d`、`z = 0`、`n ∈ %s`'
          % (cmax, vmax, tmax, list(ns)))
    print()
    tab = Counter()
    ex = []
    for L in lens:
        for R in itertools.product(cols, repeat=L):
            R = list(R)
            if not argOK(R) or dom_m(R) is None:
                continue
            if srow(R, len(R) - 1) != 2:
                continue
            z = 0
            for v in range(vmax):
                if not has_parent([(0, v, z)] + R, 2, len(R)):
                    continue
                for t in range(tmax):
                    M = Lift1([(0, v, z)] + R, t)
                    Q = M[:-1]
                    if ref.inW(Q, 2 * (v + t) + z) is not True:
                        continue
                    d = entry(M, 0, len(M) - 1) - entry(M, 0, 0)
                    e = entry(M, 1, len(M) - 1) - entry(M, 1, 0)
                    bad = [j for j in range(1, len(Q))
                           if entry(Q, 2, j) > 0 and not le1(Q, 0, j)]
                    if not bad:
                        continue
                    for n in ns:
                        T = mTower(Q, d, e, n)
                        B = Lift1(shiftr01(d * n, 0, Q), e * n)
                        for j in bad:
                            C1 = T + B[:j + 1]
                            p = len(T) + j
                            par = trio.parent(list(C1), srow(C1, p), p)
                            if par is None:
                                tab[(L, '**親なし ⟹ (C2) で無料**')] += 1
                            elif par >= len(T):
                                tab[(L, '親は**同じブロック** ⟹ 窓 < |Q|')] += 1
                            else:
                                tab[(L, '⛔ 親は**前のブロック**（復活）')] += 1
                                if len(ex) < 5:
                                    ex.append((R, v, t, n, j, Q, par, len(T)))
    print('| `|R|` | 場合 | **件数** |')
    print('|--:|---|--:|')
    for (L, k), c in sorted(tab.items()):
        print('| %d | %s | **%d** |' % (L, k, c))
    print()
    rev = sum(c for (L, k), c in tab.items() if '復活' in k)
    tot = sum(tab.values())
    print('**復活: %d / %d (%.2f%%)**' % (rev, tot, 100.0 * rev / max(tot, 1)))
    print()
    if ex:
        print('**⛔ 復活の例:**')
        for R, v, t, n, j, Q, par, lt in ex:
            print('    R=`%s` v=%d t=%d n=%d j=%d 親=%d ブロック境界=%d'
                  % (fmt(R), v, t, n, j, par, lt))
    else:
        print('> **★★★ 復活ゼロ ⟹ 第 3 の枝は消える。**')
        print('> ⟹ **枝は「親なし（(C2) で無料）」と「親は同じブロック（(C1) の測度）」の 2 つだけ。**')
    print()


if __name__ == '__main__':
    print('## (e) 第 3 の枝: 親は同じブロックか、前のブロックか')
    print()
    run(2, (2, 3, 4))
