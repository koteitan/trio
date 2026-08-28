# -*- coding: utf-8 -*-
"""課題 R10 (2): 残る「減」を作る発火の構造。どの条項の・どこの決定が
接頭辞を伸ばすと**真から偽に落ちる**のかを、条項ごとに差分で特定する。"""
import sys, os, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/g2')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, provc, r7
from rows3 import b2d3
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
print('現在の rows3.py（tiesd 既定 off）  ST_TS v<=%d len<=%d %d 個  **減 %d**'
      % (v, L, len(P), len(V)))
c = Counter()
for a, b in V:
    A, B = P[a], P[b]
    _, PA = provc.b2d3p(list(A))
    _, PB = provc.b2d3p(list(B))
    fa, fb = IM[a], IM[b]
    j = 0
    while j < len(fa) and j < len(fb) and fa[j] == fb[j]:
        j += 1
    ea = PA[j] if j < len(PA) else None
    eb = PB[j] if j < len(PB) else None
    c['左 why=%s / 右 why=%s' % (ea[2] if ea else '?', eb[2] if eb else '?')] += 1
    c['左の入力列は末尾から %s 本目' % ((len(A) - 1 - ea[1]) if ea else '?')] += 1
    c['B は A の真の接頭辞拡張: %s' % (B[:len(A)] == A)] += 1
    print()
    print(' M1 = %s' % ''.join(str(x).replace(' ', '') for x in A))
    print(' M2 = %s' % ''.join(str(x).replace(' ', '') for x in B))
    print('   j=%d  fM1[j]=%s %s' % (j, fa[j] if j < len(fa) else None, ea))
    print('         fM2[j]=%s %s' % (fb[j] if j < len(fb) else None, eb))
print()
for k in sorted(c, key=str):
    print('   %-40s %d' % (k, c[k]))
