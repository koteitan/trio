# -*- coding: utf-8 -*-
"""aw2 が壊す site を取り出し、それを浅く戻す述語を探す。"""
import sys, pickle
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
import rows3, rows3p, provh
from core import expand, show
from h7agree import agree

for k in rows3p.NX: rows3p.NX[k]=False
B = agree(rows3p.b2d3, 6, 4, 6)
for k in rows3p.NX: rows3p.NX[k]=True
C = agree(rows3p.b2d3, 6, 4, 6)
broke = sorted(B - C)
print('aw2 が壊す (A,n,m) %d 組' % len(broke))
pos = set()
for Mt, n, m in broke:
    E = tuple(tuple(x) for x in expand(Mt, n))
    for k in rows3p.NX: rows3p.NX[k]=False
    U, pr = provh.b2d3p(list(E))
    for k in rows3p.NX: rows3p.NX[k]=True
    V = tuple(rows3p.b2d3(list(E)))
    for i,(u,v) in enumerate(zip(U,V)):
        if tuple(u)!=tuple(v):
            kk,off,why,ctx,d = pr[i]
            pos.add((E, off))
print('ちがう柱 %d 個' % len(pos))
for E,off in sorted(pos):
    print('   %-58s off=%-3d p=%s' % (show([list(c) for c in E])[:58], off, E[off]))
pickle.dump(sorted(pos), open('/tmp/h1work/aw2broke.pkl','wb'))
