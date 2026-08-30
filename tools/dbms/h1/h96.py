# -*- coding: utf-8 -*-
"""**(w3) `p_rel >= 2` を出しにいく（教訓 21: 箱を伸ばす）。**

§192 の表は **`p_rel <= 1`** に乗っている。⚠ それは**私の測定であって定理ではない**。
h93 の 19017 件は `|R| ∈ {2,3,4}`・行0∈[1,2]・行1<3・行2<2 の箱。
⟹ **`|R| = 5` と、行 0・行 1 を広げて壊しにいく。**

`p_rel := parent − (n-1)*|Q|`（`j = 0`、ブロック `n` の根の行 1 の親）
h93 の「窓」との関係: **窓 `= |Q| − p_rel`**。
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


def run(lens, dmax, bmax, cmax=2, ns=(1, 2, 3), tmax=2, vmax=3, tag=''):
    cols = [(a, b, c) for a in range(1, dmax) for b in range(bmax)
            for c in range(cmax)]
    print('### %s 箱: 行0∈[1,%d]・行1<%d・行2<%d、`|R|`=%s、`v<%d`、`t<%d`、`n∈%s`'
          % (tag, dmax - 1, bmax, cmax, list(lens), vmax, tmax, list(ns)))
    print()
    tab = Counter()
    ex = []
    for L in lens:
        for R in itertools.product(cols, repeat=L):
            R = list(R)
            if not argOK(R) or dom_m(R) is None or srow(R, len(R) - 1) != 2:
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
                        p = len(T)
                        s = srow(C1, p)
                        par = trio.parent(C1, s, p)
                        if par is None:
                            tab[(L, '親なし')] += 1
                            continue
                        prel = par - (n - 1) * len(Q)
                        key = ('**p_rel = %d**' % prel) if prel <= 1 \
                            else ('⛔ **p_rel = %d (>= 2)**' % prel)
                        tab[(L, 'e=%s ・ %s' % ('0' if e == 0 else '>=1', key))] += 1
                        if prel >= 2 and len(ex) < 5:
                            ex.append((R, v, t, n, Q, d, e, par, prel))
    print('| `|R|` | 場合 | **件数** |')
    print('|--:|---|--:|')
    for (L, k), c in sorted(tab.items()):
        print('| %d | %s | **%d** |' % (L, k, c))
    tot = sum(tab.values())
    bad = sum(c for (L, k), c in tab.items() if '>= 2' in k)
    print()
    print('**分母 %d、`p_rel >= 2` は %d 件 (%.3f%%)**' % (tot, bad, 100.0*bad/max(tot,1)))
    print()
    if ex:
        print('**⛔ `p_rel >= 2` の例:**')
        for R, v, t, n, Q, d, e, par, prel in ex:
            print('    R=`%s` v=%d t=%d n=%d Q=`%s` d=%d e=%d 親=%d **p_rel=%d**'
                  % (fmt(R), v, t, n, fmt(Q), d, e, par, prel))
    else:
        print('> **`p_rel >= 2` は 0 件。**')
    print()


if __name__ == '__main__':
    print('## (w3) `p_rel >= 2` を出しにいく')
    print()
    run((5,), 3, 3, tag='(A) `|R|=5`、')
    run((2, 3, 4), 4, 4, tag='(B) 箱を広げる（行0<=3・行1<4）、')
