# -*- coding: utf-8 -*-
"""**h97 の陰性対照**: 手で作った候補の母集団は空でなかったか（教訓 23）。

⚠ h97 は「0 件」と出したが**分母を出していなかった**。母集団が空なら意味が無い。
あわせて **`S = {i : entry Q 0 i < entry Q 0 0 + d}` の最大値**を測る
（解析: **`p_rel <= max(S)`**）。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio, wref
from wref import fmt, entry, srow, has_parent, dom_m, argOK, Lift1, shiftr01
from h88 import mTower, le1
from collections import Counter

ref = wref.Ref(maxnodes=6000)
tab = Counter()
ex = []
for L in (3, 4):
    for tail0 in (2, 3):
        for tailb in range(4):
            for body in itertools.product(
                    [(1, b, c) for b in range(3) for c in range(2)], repeat=L - 1):
                R = list(body) + [(tail0, tailb, 1)]
                tab['(0) 全組合せ'] += 1
                if not argOK(R) or dom_m(R) is None:
                    tab['(1) argOK/domT で落ちる'] += 1; continue
                if srow(R, len(R) - 1) != 2:
                    tab['(2) srow != 2 で落ちる'] += 1; continue
                for v in range(3):
                    if not has_parent([(0, v, 0)] + R, 2, len(R)):
                        tab['(3) hasParent で落ちる'] += 1; continue
                    for t in range(2):
                        M = Lift1([(0, v, 0)] + R, t)
                        Q = M[:-1]
                        if ref.inW(Q, 2 * (v + t)) is not True:
                            tab['(4) Q ∈ W a で落ちる'] += 1; continue
                        tab['**(5) 母集団に入った**'] += 1
                        d = entry(M, 0, len(M) - 1) - entry(M, 0, 0)
                        e = entry(M, 1, len(M) - 1) - entry(M, 1, 0)
                        S = [i for i in range(len(Q))
                             if entry(Q, 0, i) < entry(Q, 0, 0) + d]
                        tab['  max(S) = %d（|Q|=%d）' % (max(S), len(Q))] += 1
                        for n in (1, 2, 3):
                            T = mTower(Q, d, e, n)
                            B = Lift1(shiftr01(d * n, 0, Q), e * n)
                            C1 = T + B[:1]
                            p = len(T)
                            par = trio.parent(C1, srow(C1, p), p)
                            if par is None:
                                tab['  親なし'] += 1; continue
                            prel = par - (n - 1) * len(Q)
                            tab['  **p_rel = %d**' % prel] += 1
                            if prel >= 2 and len(ex) < 3:
                                ex.append((R, v, t, n, Q, d, e, par, prel, S))
print('## h97 の陰性対照（分母つき）')
print()
wref.tally(tab, '母集団の内訳と `max(S)` / `p_rel`')
if ex:
    print('**⛔ `p_rel >= 2`:**')
    for R, v, t, n, Q, d, e, par, prel, S in ex:
        print('    R=`%s` v=%d t=%d n=%d Q=`%s` d=%d e=%d 親=%d p_rel=%d S=%s'
              % (fmt(R), v, t, n, fmt(Q), d, e, par, prel, S))
