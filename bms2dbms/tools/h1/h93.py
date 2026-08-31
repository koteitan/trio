# -*- coding: utf-8 -*-
"""**(c) `j = 0`（ブロックの根）: `hstep` は何を要求されるか。**

§260 で `hstep` の窓の前提は `0 < j` の列だけになった。⟹ **`j = 0` は無条件。**
ブロックの根を塔に足すとき、親はどこにいるのかを測る。

予想: **第 `n` ブロックの根の親は、第 `n-1` ブロックの根**（窓 = ちょうど `|Q|`）。
⟹ これは「窓 < |Q|」ではなく、**塔の再帰そのもの**。
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
                    for n in ns:
                        T = mTower(Q, d, e, n)
                        B = Lift1(shiftr01(d * n, 0, Q), e * n)
                        C1 = T + B[:1]
                        p = len(T)          # ブロックの根の位置 = n*|Q|
                        s = srow(C1, p)
                        par = trio.parent(C1, s, p)
                        if par is None:
                            k = '**親なし**'
                        else:
                            w = p - par
                            k = ('親は**1 つ前のブロックの根**（窓 = |Q|）'
                                 if par == p - len(Q)
                                 else '親の窓 = %s' % ('|Q| の倍数でない: %d' % w))
                        tab[(L, 'srow=%d ・ %s' % (s, k))] += 1
    print('| `|R|` | 場合 | **件数** |')
    print('|--:|---|--:|')
    for (L, k), c in sorted(tab.items()):
        print('| %d | %s | **%d** |' % (L, k, c))
    print()
    print('**分母: %d**' % sum(tab.values()))
    print()


if __name__ == '__main__':
    print('## (c) `j = 0`: ブロックの根の親はどこか')
    print()
    run(2, (2, 3, 4))
