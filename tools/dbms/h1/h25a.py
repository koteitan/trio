# -*- coding: utf-8 -*-
"""H25: `len<=11` で残る 24 件の逆転を分類する（柱単調性 CM）。"""
import sys, time, pickle
from collections import Counter
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/g2')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, provc, core, r7
from rows3 import copy_head, top_level, term_top, par0, is_branch, is_w_col
from core import show

P = r7.stts_pool(5, 11)
IM = []
for i, M in enumerate(P):
    if i % 50000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    IM.append(tuple(tuple(c) for c in rows3.b2d3(list(M))))
o = sorted(range(len(P)), key=lambda i: P[i])
seq = [IM[i] for i in o]
bad = [i for i in range(len(seq) - 1) if seq[i] >= seq[i + 1]]
print('len<=11 の逆転 %d 件' % len(bad))
c = Counter()
rows = []
for i in bad:
    M1, M2 = P[o[i]], P[o[i + 1]]
    # 共通接頭辞の長さ
    p = 0
    while p < min(len(M1), len(M2)) and M1[p] == M2[p]:
        p += 1
    C1, PR1 = provc.b2d3p(list(M1))
    C2, PR2 = provc.b2d3p(list(M2))
    k = 0
    while k < min(len(C1), len(C2)) and C1[k] == C2[k]:
        k += 1
    w1 = PR1[k] if k < len(PR1) else None
    w2 = PR2[k] if k < len(PR2) else None
    kind = ('接頭辞' if p == min(len(M1), len(M2)) else '分岐(CM)')
    c[(kind, str(w1[2] if w1 else None), str(w2[2] if w2 else None))] += 1
    c['_' + kind] += 1
    rows.append((M1, M2, p, k, w1, w2, C1[k] if k < len(C1) else None,
                 C2[k] if k < len(C2) else None))
print()
for k2, v in c.most_common():
    print('   %-56s %d' % (str(k2), v))
print()
for M1, M2, p, k, w1, w2, a, b in rows[:5]:
    print('  共通接頭辞 %d 列 / 像のずれ k=%d' % (p, k))
    print('    M1 = %s' % show([list(x) for x in M1]))
    print('    M2 = %s' % show([list(x) for x in M2]))
    print('    f M1[k]=%s (%s)   f M2[k]=%s (%s)' % (a, w1, b, w2))
    if p < len(M1) and p < len(M2):
        print('    分岐の柱: M1[%d]=%s / M2[%d]=%s' % (p, M1[p], p, M2[p]))
    print()
pickle.dump(rows, open('/tmp/h1work/h25rows.pkl', 'wb'))
