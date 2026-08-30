import sys, pickle
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, provh
from rows3 import is_branch, term_top, ANCHOR
from core import expand, show
import h9spell

MODE = sys.argv[3] if len(sys.argv)>3 else 'term'
def prev_of2(Mo, off, memo, skip_tie=None, nxts=None):
    for j in range(off - 1, -1, -1):
        if MODE == 'term' and term_top(Mo, j): return None
        if MODE == 'root' and Mo[j][0] == 0: return None      # newterm だけで切る
        if MODE == 'never' and False: pass
        if is_branch(Mo[j]):
            if skip_tie is not None and j in skip_tie: continue
            return 0 if h9spell.spell(Mo, j, memo, skip_tie, nxts) else 1
    return None
h9spell.prev_of = prev_of2

LIM=int(sys.argv[1]); NMAX=int(sys.argv[2])
A=sorted(rows3.gen3('BMS',LIM,zcap=1), key=rows3.key)
c=Counter(); ex={}
for M in A:
    Mt=tuple(map(tuple,M))
    for n in range(0, NMAX+1):
        E = Mt if n==0 else tuple(tuple(x) for x in expand(Mt,n))
        U,pr = provh.b2d3p(list(E))
        memo={}; tie={j for (kk,j,why,ctx,d) in pr if d is not None and d.get('why')=='tie'}
        nxts={j:(tuple(d['nxt']) if d['nxt'] is not None else None) for (kk,j,why,ctx,d) in pr if d is not None and 'nxt' in d}
        for kk,off,why,ctx,d in pr:
            if kk!='body' or d is None or d.get('why')=='tie': continue
            got=d['shallow']; want=h9spell.spell(E,off,memo,tie,nxts)
            c[(got,want)]+=1
            if got!=want: ex.setdefault((E,off),(got,want,d))
print('MODE=%s  決定 %d 本  食い違い %d 本   %s' % (MODE, sum(c.values()), sum(v for k,v in c.items() if k[0]!=k[1]), dict(c)))
