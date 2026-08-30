# -*- coding: utf-8 -*-
"""`SeqEmbT3` を ST_TS v<=5 len<=11（1882196 個）で検証（順序だけ。isstd は外す）。"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7
from rows3 import b2d3
v, L = int(sys.argv[1]), int(sys.argv[2])
t0 = time.time(); P = r7.stts_pool(v, L)
print('母集団 ST_TS v<=%d len<=%d  **%d 個**  (%.0fs)'
      % (v, L, len(P), time.time() - t0), flush=True)
t0 = time.time(); IM = []
for i, M in enumerate(P):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    IM.append(tuple(tuple(c) for c in b2d3(list(M))))
print('  像 %.0fs' % (time.time() - t0), flush=True)
t0 = time.time()
up = dn = eq = 0; ex = []
for i in range(len(P) - 1):          # P は既に seqlex 昇順
    a, b = IM[i], IM[i + 1]
    if a < b:
        up += 1
    elif a == b:
        eq += 1
        if len(ex) < 3: ex.append(('eq', P[i], P[i + 1]))
    else:
        dn += 1
        if len(ex) < 3: ex.append(('dn', P[i], P[i + 1]))
print('== (→) 隣 %d 対: 増 %d / **等 %d** / **減 %d** -> 破れ **%d**  (%.0fs)'
      % (len(P) - 1, up, eq, dn, eq + dn, time.time() - t0), flush=True)
print('== 陽性対照（像が狭義減少を要求）: 破れ %d / %d' % (up + eq, len(P) - 1), flush=True)
t0 = time.time()
o2 = sorted(range(len(P)), key=lambda i: IM[i])
d2 = sum(1 for i in range(len(o2) - 1) if P[o2[i]] > P[o2[i + 1]])
e2 = sum(1 for i in range(len(o2) - 1) if P[o2[i]] == P[o2[i + 1]])
print('== (←) 隣 %d 対: **減 %d / 等 %d** -> 破れ **%d**  (%.0fs)'
      % (len(o2) - 1, d2, e2, d2 + e2, time.time() - t0), flush=True)
for k, a, b in ex:
    print('   %s M1=%s' % (k, ''.join(str(x).replace(' ', '') for x in a)))
    print('      M2=%s' % ''.join(str(x).replace(' ', '') for x in b))
