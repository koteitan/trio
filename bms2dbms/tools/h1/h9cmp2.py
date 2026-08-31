import sys, pickle
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, provh
from rows3 import is_branch
from core import expand, show
from h9spell import spell, prev_of

LIM=int(sys.argv[1]) if len(sys.argv)>1 else 6
NMAX=int(sys.argv[2]) if len(sys.argv)>2 else 3
A=sorted(rows3.gen3('BMS',LIM,zcap=1), key=rows3.key)
c=Counter(); ex={}
for i,M in enumerate(A):
    Mt=tuple(map(tuple,M))
    for n in range(0, NMAX+1):
        E = Mt if n==0 else tuple(tuple(x) for x in expand(Mt,n))
        U,pr = provh.b2d3p(list(E))
        memo={}; tie={j for (kk,j,why,ctx,d) in pr if d is not None and d.get('why')=='tie'}
        nxts={j: (tuple(d['nxt']) if d['nxt'] is not None else None) for (kk,j,why,ctx,d) in pr if d is not None and 'nxt' in d}
        for pe in pr:
            kk,off,why,ctx,d = pe
            if kk!='body' or d is None: continue
            if d.get('why')=='tie': continue
            got = d['shallow']
            want = spell(E, off, memo, tie, nxts)
            c[(got, want)] += 1
            if got != want: ex.setdefault((E,off), (got,want,d))
print('分岐列の決定 %d 本' % sum(c.values()))
print('(conv3 の shallow, spell の shallow):', dict(c))
bad=[k for k in ex]
print('食い違い %d 本（相異なる (行列, off)）' % len(bad))
pickle.dump(ex, open('/tmp/h1work/h9diff2.pkl','wb'))
for (E,off),(g,w,d) in list(ex.items())[:8]:
    print('   %-58s off=%-3d p=%s conv3=%s spell=%s why=%s prev=%s'
          % (show([list(x) for x in E])[:58], off, E[off], g, w, d['why'], d['prev0']))
