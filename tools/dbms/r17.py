# -*- coding: utf-8 -*-
"""課題 R11 の検証: 課題 H の v19/v20 で `SeqEmbT3` が真になったかを
**母数を 4.5 倍に広げて**独立に確かめる（`ST_TS v<=5 len<=11` の 1882196 個）。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7
from rows3 import b2d3

v, L = int(sys.argv[1]), int(sys.argv[2])
t0 = time.time()
P = r7.stts_pool(v, L)
print('母集団 ST_TS v<=%d len<=%d  **%d 個**  (%.0fs)' % (v, L, len(P), time.time() - t0),
      flush=True)
t0 = time.time()
IM = []
for i, M in enumerate(P):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    IM.append(tuple(tuple(c) for c in b2d3(list(M))))
print('  像を計算 %.0fs' % (time.time() - t0), flush=True)
o = sorted(range(len(P)), key=lambda i: P[i])
up = dn = eq = 0
ex = []
for i in range(len(o) - 1):
    a, b = IM[o[i]], IM[o[i + 1]]
    if a < b:
        up += 1
    elif a == b:
        eq += 1
        if len(ex) < 3:
            ex.append(('eq', P[o[i]], P[o[i + 1]]))
    else:
        dn += 1
        if len(ex) < 3:
            ex.append(('dn', P[o[i]], P[o[i + 1]]))
print('== (→) 隣 %d 対: 増 %d / **等 %d** / **減 %d** -> 破れ **%d**'
      % (len(o) - 1, up, eq, dn, eq + dn))
o2 = sorted(range(len(P)), key=lambda i: IM[i])
up2 = dn2 = eq2 = 0
for i in range(len(o2) - 1):
    a, b = P[o2[i]], P[o2[i + 1]]
    if a < b:
        up2 += 1
    elif a == b:
        eq2 += 1
    else:
        dn2 += 1
print('== (←) 隣 %d 対: 増 %d / 等 %d / **減 %d** -> 破れ **%d**'
      % (len(o2) - 1, up2, eq2, dn2, eq2 + dn2))
print('== 陽性対照（像が狭義**減少**を要求）: 破れ %d / %d' % (up + eq, len(o) - 1))
ns = sum(1 for B in IM if not core.isstd(B, 'DBMS'))
print('== 非標準の像 %d / %d' % (ns, len(IM)))
for k, a, b in ex:
    print('   %s M1=%s' % (k, ''.join(str(x).replace(' ', '') for x in a)))
    print('      M2=%s' % ''.join(str(x).replace(' ', '') for x in b))
