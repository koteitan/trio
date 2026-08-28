# -*- coding: utf-8 -*-
"""H12: 破れ (A,m,T) の**証人** B = d2b3(T) と conv3(B) を柱ごとに突き合わせる。

`d2b3` は長さが揃うので整列できる（H2 の「族 β の証人は d2b3(T)」）。
最初にずれた柱の出どころ（kind, off, why, ctx）と、あるべき柱を並べる。
"""
import sys, pickle
from collections import Counter
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/g2')
import rows3, provc, rows3F, inv3
from rows3 import is_branch, par0, copy_head, term_top, is_w_col
from core import expand, show, isstd

bad = sorted(pickle.load(open('/tmp/h1work/img54p.pkl', 'rb')),
             key=lambda e: (len(e[0]), e[0], e[1]))
rows = []
c = Counter()
for A, m, Tg in bad:
    Tg = tuple(map(tuple, Tg))
    B = inv3.d2b3([list(x) for x in Tg])
    if B is None:
        c['d2b3 が返さない'] += 1
        continue
    Bt = tuple(tuple(x) for x in B)
    if not isstd(Bt, 'BMS'):
        c['証人が BMS 標準形でない'] += 1
        continue
    if any(x[2] > 1 for x in Bt):
        c['証人が z>=2'] += 1
        continue
    C, PR = provc.b2d3p(list(Bt))
    if C == Tg:
        c['素で当たっている'] += 1
        continue
    k = 0
    while k < min(len(C), len(Tg)) and C[k] == Tg[k]:
        k += 1
    if k >= len(PR):
        c['ずれが記録の外'] += 1
        continue
    kind, off, why, ctx = PR[k]
    out, rec = rows3F.b2d3F(list(Bt))
    R = next((x for x in rec if x['off'] == off), None)
    e = dict(A=tuple(map(tuple, A)), m=m, T=Tg, B=Bt, C=C, k=k, kind=kind,
             off=off, why=why, ctx=ctx, want=Tg[k] if k < len(Tg) else None,
             got=C[k], col=Bt[off], R=R, lenB=len(Bt),
             dlen=len(C) - len(Tg))
    c['読めた'] += 1
    rows.append(e)
pickle.dump(rows, open('/tmp/h1work/h12rows.pkl', 'wb'))
print('破れ %d 対:' % len(bad))
for k, v in c.most_common():
    print('   %-26s %d' % (k, v))
print()
print('長さの差 len(C)-len(T): %s' % Counter(r['dlen'] for r in rows).most_common())
print('kind: %s' % Counter(r['kind'] for r in rows).most_common())
print('ctx : %s' % Counter(str(r['ctx']) for r in rows).most_common())
print('why : %s' % Counter(str(r['why']) for r in rows).most_common())
print('柱の型: %s' % Counter(
    ('branch' if is_branch(r['col']) else
     ('w' if is_w_col(r['col']) else str(r['col']))) for r in rows).most_common(8))
print('深さのずれ want-got: %s'
      % Counter(r['want'][0] - r['got'][0] for r in rows if r['want']).most_common())
print('行1のずれ  want-got: %s'
      % Counter(r['want'][1] - r['got'][1] for r in rows if r['want']).most_common())
print('first: %s' % Counter(r['R']['first'] if r['R'] else None for r in rows).most_common())
