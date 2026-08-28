# -*- coding: utf-8 -*-
"""H13: ImgCofinalT で本当に破れている A だけで、証人 d2b3(T) の逆算をやり直す。"""
import sys, pickle
from collections import Counter
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/g2')
import rows3, provc, inv3
from rows3 import is_branch, is_w_col
from core import expand, show, isstd

cof = set(pickle.load(open('/tmp/h1work/cof6.pkl', 'rb')))
bad = pickle.load(open('/tmp/h1work/img54p.pkl', 'rb'))
bad = [e for e in bad if tuple(map(tuple, e[0])) in
       set(tuple(map(tuple, A)) for A in cof)]
print('ImgCofinalT で本当に破れている A %d 個 -> 対 %d 件' % (len(cof), len(bad)))
c = Counter()
rows = []
for A, m, Tg in bad:
    Tg = tuple(map(tuple, Tg))
    B = inv3.d2b3([list(x) for x in Tg])
    if B is None:
        c['d2b3 が返さない'] += 1
        continue
    Bt = tuple(tuple(x) for x in B)
    if not isstd(Bt, 'BMS') or any(x[2] > 1 for x in Bt):
        c['証人が BMS 標準形でない'] += 1
        continue
    C, PR = provc.b2d3p(list(Bt))
    if C == Tg:
        c['素で当たる'] += 1
        continue
    k = 0
    while k < min(len(C), len(Tg)) and C[k] == Tg[k]:
        k += 1
    if k >= len(PR):
        c['ずれが記録の外'] += 1
        continue
    kind, off, why, ctx = PR[k]
    c['読めた'] += 1
    rows.append((Bt, Tg, C, k, kind, off, why, ctx))
for k, v in c.most_common():
    print('   %-24s %d' % (k, v))
print()
print('kind: %s' % Counter(r[4] for r in rows).most_common())
print('ctx : %s' % Counter(str(r[7]) for r in rows).most_common())
print('why : %s' % Counter(str(r[6]) for r in rows).most_common())
print('柱  : %s' % Counter(('branch' if is_branch(r[0][r[5]]) else
                           ('w' if is_w_col(r[0][r[5]]) else str(r[0][r[5]])))
                          for r in rows).most_common(6))
print('深さのずれ: %s' % Counter(r[1][r[3]][0] - r[2][r[3]][0]
                              for r in rows if r[3] < len(r[1])).most_common())
pickle.dump(rows, open('/tmp/h1work/h13rows.pkl', 'wb'))
