# -*- coding: utf-8 -*-
"""len<=11 で出た 24 件の破れの構造。"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/g2')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, provc, r7
from rows3 import b2d3
from collections import Counter
P = r7.stts_pool(5, 11)
IM = []
for i, M in enumerate(P):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    IM.append(tuple(tuple(c) for c in b2d3(list(M))))
V = [(i, i + 1) for i in range(len(P) - 1) if IM[i] > IM[i + 1]]
print('ST_TS v<=5 len<=11  %d 個  **減 %d**' % (len(P), len(V)), flush=True)
c = Counter()
for a, b in V:
    A, B = P[a], P[b]
    fa, fb = IM[a], IM[b]
    j = 0
    while j < len(fa) and j < len(fb) and fa[j] == fb[j]:
        j += 1
    _, PA = provc.b2d3p(list(A))
    _, PB = provc.b2d3p(list(B))
    ea = PA[j] if j < len(PA) else None
    eb = PB[j] if j < len(PB) else None
    # 入力側で最初に食い違う列
    k = 0
    while k < len(A) and k < len(B) and A[k] == B[k]: k += 1
    c['接頭辞拡張か: %s' % (B[:len(A)] == A or A[:len(B)] == B)] += 1
    c['入力の分岐位置 k と site off が同じ: %s' % (ea and ea[1] == k)] += 1
    c['左 why=%s / 右 why=%s' % (ea[2] if ea else '?', eb[2] if eb else '?')] += 1
    c['列数 (%d,%d)' % (len(A), len(B))] += 1
    if c['_p'] < 4:
        c['_p'] += 1
        print()
        print(' M1 = %s' % ''.join(str(x).replace(' ', '') for x in A))
        print(' M2 = %s' % ''.join(str(x).replace(' ', '') for x in B))
        print('   入力が食い違う列 k=%d: M1[k]=%s M2[k]=%s' % (k, A[k] if k < len(A) else None, B[k] if k < len(B) else None))
        print('   像が食い違う j=%d: fM1[j]=%s %s' % (j, fa[j], ea))
        print('                     fM2[j]=%s %s' % (fb[j], eb))
print()
for k in sorted(c, key=str):
    if not k.startswith('_'):
        print('   %-46s %d' % (k, c[k]))
