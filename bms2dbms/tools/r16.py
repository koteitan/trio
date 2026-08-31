# -*- coding: utf-8 -*-
"""課題 R11 (1): 7 件の減で `aw_flip` の**各リテラル**の真偽を M1 / M2 で並べる。

`aw_flip` の第 1 選言 = L1 & L2
    L1 = is_w_col(Mo[-1])                       行列の末尾の列が「x w」
    L2 = not any(copy_head(Mo,t) for t>off)     自分より後ろに写しの頭が無い
`aw_flip` が **True -> deep**。単調にするには「伸ばしても True のまま」が要る。
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/g2')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, provc, r7
from rows3 import b2d3, is_w_col, copy_head, par0
from collections import Counter

v, L = int(sys.argv[1]), int(sys.argv[2])
P = r7.stts_pool(v, L)
IM = []
for i, M in enumerate(P):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    IM.append(tuple(tuple(c) for c in b2d3(list(M))))
o = sorted(range(len(P)), key=lambda i: P[i])
V = [(o[i], o[i + 1]) for i in range(len(o) - 1) if IM[o[i]] > IM[o[i + 1]]]
print('ST_TS v<=%d len<=%d %d 個  **減 %d**' % (v, L, len(P), len(V)))


def lits(M, off):
    n = len(M)
    L1 = is_w_col(M[-1])
    L2 = not any(copy_head(M, t) for t in range(off + 1, n))
    L1p = any(is_w_col(M[t]) for t in range(off + 1, n))   # 単調版の候補
    a01 = par0(M, off)
    L3 = not (a01 >= 0 and off - a01 > 3)
    return L1, L2, L1p, L3


c = Counter()
for a, b in V:
    A, B = P[a], P[b]
    _, PA = provc.b2d3p(list(A))
    fa, fb = IM[a], IM[b]
    j = 0
    while j < len(fa) and j < len(fb) and fa[j] == fb[j]:
        j += 1
    off = PA[j][1]
    la, lb = lits(A, off), lits(B, off)
    nm = ('L1=is_w_col(Mo[-1])', 'L2=¬∃copy_head(>off)',
          "L1'=∃is_w_col(>off)", 'L3=行0の親が近い')
    print()
    print(' M1 = %s' % ''.join(str(x).replace(' ', '') for x in A))
    print(' M2 = %s' % ''.join(str(x).replace(' ', '') for x in B))
    print('   site off=%d  why=%s -> %s' % (off, PA[j][2], fa[j]))
    for k in range(4):
        flip = '  ← **真→偽（犯人）**' if (la[k] and not lb[k]) else ''
        print('   %-24s M1=%-5s M2=%-5s%s' % (nm[k], la[k], lb[k], flip))
        if la[k] and not lb[k]:
            c['犯人 ' + nm[k]] += 1
print()
for k in sorted(c, key=str):
    print('   %-30s %d / %d' % (k, c[k], len(V)))
