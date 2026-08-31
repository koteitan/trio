# -*- coding: utf-8 -*-
"""**(w3) 修正した機構（行 1 の窓）で `p_rel >= 2` を狙い撃つ。**

機構: 錐の中の列 `i` が候補になるには
    **`entry Q 1 0 < entry Q 1 i < entry Q 1 0 + e`**（`le1` が狭義増加を要求するので）
⟹ **`e` を大きくすれば窓が広がる** ⟹ `i = 2` 以降も候補になれるはず。

狙い: `v = 0`（`entry Q 1 0` を小さく）、`R` の末尾列の行 1 を大きく（`e` を大きく）、
`R.dropLast` の行 1 を 1,2,… と**増加**させる（錐の中に入れる）、
`R.dropLast` の行 0 を `d` より小さく（行 0 の祖先性）。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio, wref
from wref import fmt, entry, srow, has_parent, dom_m, argOK, Lift1, shiftr01
from h88 import mTower, le1
from collections import Counter

ref = wref.Ref(maxnodes=8000)
tab = Counter()
ex = []
# R.dropLast: 行 0 は 1..2、行 1 は増加列、行 2 は 0/1
body_cols = [(a, b, c) for a in (1, 2) for b in range(1, 4) for c in range(2)]
for L in (3,):
    for body in itertools.product(body_cols, repeat=L - 1):
        for tail0 in (2, 3, 4):
            for tailb in range(3, 7):
                R = list(body) + [(tail0, tailb, 1)]
                tab['(0) 全組合せ'] += 1
                if not argOK(R) or dom_m(R) is None or srow(R, len(R) - 1) != 2:
                    tab['(1) argOK/domT/srow で落ちる'] += 1; continue
                for v in (0, 1):
                    if not has_parent([(0, v, 0)] + R, 2, len(R)):
                        tab['(2) hasParent で落ちる'] += 1; continue
                    for t in (0, 1):
                        M = Lift1([(0, v, 0)] + R, t)
                        Q = M[:-1]
                        if ref.inW(Q, 2 * (v + t)) is not True:
                            tab['(3) Q ∈ W a で落ちる'] += 1; continue
                        tab['**(4) 母集団**'] += 1
                        d = entry(M, 0, len(M) - 1) - entry(M, 0, 0)
                        e = entry(M, 1, len(M) - 1) - entry(M, 1, 0)
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
                            if prel >= 2 and len(ex) < 4:
                                ex.append((R, v, t, n, Q, d, e, par, prel))
print('## (w3) 行 1 の窓を広げて `p_rel >= 2` を狙う')
print()
wref.tally(tab, '分母と `p_rel` の分布')
if ex:
    print('**⛔⛔ `p_rel >= 2` の反例:**')
    for R, v, t, n, Q, d, e, par, prel in ex:
        print('    R=`%s` v=%d t=%d n=%d' % (fmt(R), v, t, n))
        print('      Q=`%s` (|Q|=%d) d=%d **e=%d** 親=%d **p_rel=%d**'
              % (fmt(Q), len(Q), d, e, par, prel))
else:
    print('> `p_rel >= 2` は出ませんでした。')
