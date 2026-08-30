# -*- coding: utf-8 -*-
"""**(c) の例外: ブロックの根の親が「1 つ前のブロックの根」でない場合。**

h93 で `j = 0` の親は 99.6% が「1 つ前のブロックの根」（窓 = |Q|）だが、
**0.4% は窓が 1 や 2**（＝ 前のブロックの**末尾付近**）だった。
⟹ L3 の §187「`j = 0` では接頭辞が 1 ブロック減る」が破れる可能性がある。

**具体例を出して確かめる。**
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import fmt, entry, srow, has_parent, dom_m, argOK, Lift1, shiftr01
from h88 import mTower, le1

ref = wref.Ref(maxnodes=4000)
cols = [(a, b, c) for a in range(1, 3) for b in range(3) for c in range(2)]
found = 0
for L in (2, 3):
    for R in itertools.product(cols, repeat=L):
        if found >= 4:
            break
        R = list(R)
        if not argOK(R) or dom_m(R) is None or srow(R, len(R) - 1) != 2:
            continue
        z = 0
        for v in range(3):
            if not has_parent([(0, v, z)] + R, 2, len(R)):
                continue
            for t in range(2):
                M = Lift1([(0, v, z)] + R, t)
                Q = M[:-1]
                if ref.inW(Q, 2 * (v + t) + z) is not True:
                    continue
                d = entry(M, 0, len(M) - 1) - entry(M, 0, 0)
                e = entry(M, 1, len(M) - 1) - entry(M, 1, 0)
                for n in (1, 2, 3):
                    T = mTower(Q, d, e, n)
                    B = Lift1(shiftr01(d * n, 0, Q), e * n)
                    C1 = T + B[:1]
                    p = len(T)
                    s = srow(C1, p)
                    par = trio.parent(C1, s, p)
                    if par is not None and par != p - len(Q) and found < 4:
                        found += 1
                        print('⛔ R=`%s` v=%d z=%d t=%d d=%d e=%d n=%d' %
                              (fmt(R), v, z, t, d, e, n))
                        print('   Q  = `%s`  (|Q|=%d)' % (fmt(Q), len(Q)))
                        print('   塔+根 = `%s`' % fmt(C1))
                        print('   根の位置 p=%d  srow=%d  **親=%d**  窓=%d'
                              ' （1つ前のブロックの根なら %d）'
                              % (p, s, par, p - par, p - len(Q)))
                        print('   ⟹ 親は第 %d ブロックの %d 列目'
                              % (par // len(Q), par % len(Q)))
                        print()
