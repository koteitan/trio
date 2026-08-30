# -*- coding: utf-8 -*-
"""tt が壊す 9 site を取り出し、`term_top` の deep 判定を覆す述語 Q を探す。
   正例 = 壊れた 9 site（浅くすべき）、負例 = term_top が正しく deep と言う 2463 site。"""
import sys, pickle
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, rows3m, provh
from core import expand, show
from rows3 import is_branch, term_top

def p0_shallow(Mo, off):
    return off + 1 >= len(Mo) or term_top(Mo, off + 1)

# 1) tt が壊す (A,n,m) を集めて、その中で tt と現行がちがう柱を取る
from h7agree import agree
for k in rows3m.MX: rows3m.MX[k]=False
B = agree(rows3m.b2d3, 6, 4, 6)
for k in rows3m.MX: rows3m.MX[k]=(k=='tt')
C = agree(rows3m.b2d3, 6, 4, 6)
broke = sorted(B - C)
print('tt が壊す (A,n,m) %d 組' % len(broke))
pos = set()
for Mt, n, m in broke:
    E = tuple(tuple(x) for x in expand(Mt, n))
    for k in rows3m.MX: rows3m.MX[k]=False
    U, pr = provh.b2d3p(list(E))
    for k in rows3m.MX: rows3m.MX[k]=(k=='tt')
    V = tuple(rows3m.b2d3(list(E)))
    for i,(u,v) in enumerate(zip(U,V)):
        if tuple(u)!=tuple(v):
            kk,off,why,ctx,d = pr[i]
            pos.add((E, off))
print('ちがう柱（相異なる (行列, off)）%d 個' % len(pos))
for E,off in sorted(pos)[:12]:
    print('   %-58s off=%-3d p=%s nxt=%s  term_top(nxt)=%s'
          % (show([list(c) for c in E])[:58], off, E[off],
             E[off+1] if off+1<len(E) else None,
             term_top(E,off+1) if off+1<len(E) else 'None'))
pickle.dump(sorted(pos), open('/tmp/h1work/ttbroke.pkl','wb'))
