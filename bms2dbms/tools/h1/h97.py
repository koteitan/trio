# -*- coding: utf-8 -*-
"""**(w3) 手で作った `p_rel >= 2` の候補を当てる。**

解析: ブロック `k` の**末尾列**が次のブロックの根の行 0 の親になれば `p_rel = |Q|-1`。
そのためには `entry Q 0 (|Q|-1) < entry Q 0 0 + d`、すなわち **`d >= 2`** で
`Q` の末尾列の行 0 が小さければよい。⟹ `|Q| >= 3` なら `p_rel >= 2`。

`Q = (0,v,z) :: R.dropLast`、`d = entry R 0 (|R|-1)`、`e = entry R 1 (|R|-1) - v`。
⟹ **`R` の末尾列の行 0 を 2 以上、`R.dropLast` の行 0 を 1 にする。**
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import fmt, entry, srow, has_parent, dom_m, argOK, Lift1, shiftr01
from h88 import mTower, le1

ref = wref.Ref(maxnodes=6000)
found = 0
print('## 手で作った候補（`R.dropLast` の行 0 = 1、`R` の末尾列の行 0 >= 2）')
print()
for L in (3, 4):
    for tail0 in (2, 3):
        for tailb in range(4):
            for body in itertools.product(
                    [(1, b, c) for b in range(3) for c in range(2)], repeat=L - 1):
                R = list(body) + [(tail0, tailb, 1)]
                if not argOK(R) or dom_m(R) is None or srow(R, len(R) - 1) != 2:
                    continue
                for v in range(3):
                    if not has_parent([(0, v, 0)] + R, 2, len(R)):
                        continue
                    for t in range(2):
                        M = Lift1([(0, v, 0)] + R, t)
                        Q = M[:-1]
                        a = 2 * (v + t)
                        if ref.inW(Q, a) is not True:
                            continue
                        d = entry(M, 0, len(M) - 1) - entry(M, 0, 0)
                        e = entry(M, 1, len(M) - 1) - entry(M, 1, 0)
                        for n in (1, 2, 3):
                            T = mTower(Q, d, e, n)
                            B = Lift1(shiftr01(d * n, 0, Q), e * n)
                            C1 = T + B[:1]
                            p = len(T)
                            par = trio.parent(C1, srow(C1, p), p)
                            if par is None:
                                continue
                            prel = par - (n - 1) * len(Q)
                            if prel >= 2 and found < 6:
                                found += 1
                                print('⛔ **p_rel = %d** ── R=`%s` v=%d t=%d n=%d'
                                      % (prel, fmt(R), v, t, n))
                                print('   Q=`%s` (|Q|=%d) d=%d e=%d  親=%d 窓=%d'
                                      % (fmt(Q), len(Q), d, e, par, p - par))
                                print('   塔+根 = `%s`' % fmt(C1))
                                print()
if found == 0:
    print('> 手で作った範囲では `p_rel >= 2` は出ませんでした。')
