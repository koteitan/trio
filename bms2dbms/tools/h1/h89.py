# -*- coding: utf-8 -*-
"""**(C2) の詰め: 「塔の中で親を持つ」⟺「`Q` の中で親を持つ」か（2x2 の表）。**

h88 で「錐の外の 行 2 正の列」は塔の中でも 99.5% 孤児と分かった。
分母 440 のうち 塔で復活 2、`Q` で孤児 438。数は合うが、**同じ 2 件かは未確認**。
⟹ **2x2 の表を出して、対応が本当に 1 対 1 かを見る。**

対応が成り立つなら:

    **塔は新しい親を作らない** ⟹ (C2) は「`Q` の中で親を持つか」だけに帰着する
    ⟹ `Q` で孤児なら `snoc_of_open`（`L105Cap.lean:166`）で**無料**

⚠ `|R|=4` まで伸ばす（教訓 21）。⚠ 分母を必ず（教訓 23）。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
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
                            inQ = has_parent(Q[:j + 1], 2, j)
                            inT = has_parent(C1, srow(C1, p), p)
                            tab[(L, inQ, inT)] += 1
                            if inQ != inT and len(ex) < 5:
                                ex.append((R, v, t, n, j, Q, d, e, inQ, inT))
    print('| `|R|` | `Q` で親あり | 塔で親あり | **件数** |')
    print('|--:|--:|--:|--:|')
    for (L, a, b), c in sorted(tab.items()):
        print('| %d | %s | %s | **%d** |'
              % (L, 'はい' if a else 'いいえ', 'はい' if b else 'いいえ', c))
    print()
    mism = sum(c for (L, a, b), c in tab.items() if a != b)
    tot = sum(tab.values())
    print('**食い違い: %d / %d (%.2f%%)**' % (mism, tot, 100.0 * mism / max(tot, 1)))
    print()
    if ex:
        print('**⛔ 食い違いの例:**')
        for R, v, t, n, j, Q, d, e, a, b in ex:
            print('    R=`%s` v=%d t=%d n=%d j=%d Q=`%s` d=%d e=%d  Q:%s 塔:%s'
                  % (fmt(R), v, t, n, j, fmt(Q), d, e, a, b))
    else:
        print('> **★★ 食い違いゼロ ⟹ 塔は新しい親を作らない。**')
        print('> ⟹ **`Q` で孤児なら塔でも孤児 ⟹ `snoc_of_open` で無料。**')
    print()


if __name__ == '__main__':
    print('## (C2) の詰め: 「塔で親あり」⟺「`Q` で親あり」か')
    print()
    run(2, (2, 3, 4))
