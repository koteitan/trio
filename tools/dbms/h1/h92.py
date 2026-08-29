# -*- coding: utf-8 -*-
"""**(g) の残り: 錐の外の列で `srow = 0` は起きるか。**

§257/§258 で、錐の外の列の **行 1・行 2** の親は必ず同じブロックと分かった（緑）。
⚠ **行 0（`srow = 0`）だけ別**: `nextrel0` は `le1` を要求しないので同じ議論が効かない。

⟹ **`srow = 0` の錐の外の列が実際に起きるかを測る。** 起きなければ (g) は閉じる。

    `srow(c) = 0` ⟺ `c.2.1 = 0` かつ `c.2.2 = 0`（`Trio.lean:81`）

⚠ 塔のブロック `k` の列は `Lift1 (shiftr01 (d*k) 0 Q) (e*k)`。
　 錐の外の列は行 1 が持ち上がらないので、**`Q` の行 1 がそのまま残る**。
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


def run(cmax, lens, ns=(1, 2), tmax=2, vmax=3):
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
                    out = [j for j in range(1, len(Q)) if not le1(Q, 0, j)]
                    if not out:
                        continue
                    for n in ns:
                        T = mTower(Q, d, e, n)
                        B = Lift1(shiftr01(d * n, 0, Q), e * n)
                        for j in out:
                            C1 = T + B[:j + 1]
                            p = len(T) + j
                            s = srow(C1, p)
                            par = trio.parent(C1, s, p)
                            key = 'srow=%d ・ %s' % (
                                s, '親なし' if par is None
                                else ('**同じブロック**' if par >= len(T)
                                      else '⛔ **前のブロック**'))
                            tab[(L, key)] += 1
                            if s == 0 and par is not None and par < len(T) \
                                    and len(ex) < 5:
                                ex.append((R, v, t, n, j, Q, par, len(T)))
    print('| `|R|` | 場合 | **件数** |')
    print('|--:|---|--:|')
    for (L, k), c in sorted(tab.items()):
        print('| %d | %s | **%d** |' % (L, k, c))
    print()
    tot = sum(tab.values())
    s0 = sum(c for (L, k), c in tab.items() if k.startswith('srow=0'))
    bad = sum(c for (L, k), c in tab.items() if '前のブロック' in k)
    print('**分母（錐の外の列 × `n`）: %d**' % tot)
    print('**`srow = 0` の列: %d (%.2f%%)**' % (s0, 100.0 * s0 / max(tot, 1)))
    print('**⛔ 前のブロックから親が来る: %d (%.2f%%)**' % (bad, 100.0 * bad / max(tot, 1)))
    print()
    if ex:
        print('**⛔ `srow=0` で復活する例:**')
        for R, v, t, n, j, Q, par, lt in ex:
            print('    R=`%s` v=%d t=%d n=%d j=%d 親=%d 境界=%d'
                  % (fmt(R), v, t, n, j, par, lt))
    print()


if __name__ == '__main__':
    print('## (g) 錐の外の列の `srow` 分布と、親の出どころ')
    print()
    run(2, (2, 3, 4))
