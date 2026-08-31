import sys, os, pickle
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, rows3e2
from core import expand
TAG=os.environ['TAG']
b0=pickle.load(open('/tmp/h1work/ag_v18_7.pkl','rb'))
s0=pickle.load(open('/tmp/h1work/ag_%s_7.pkl'%TAG,'rb'))
br=sorted(b0-s0, key=lambda e:(len(e[0]),e))
NEG=set()
for A,n,m in br:
    E=tuple(tuple(x) for x in expand(A,n))
    bA=rows3e2.b2d3e(list(A), sites=set())[0]; bE=rows3e2.b2d3e(list(E), sites=set())[0]
    tgt=tuple(expand(bA,m))
    for off,_,_ in rows3e2.b2d3e(list(E))[1]:
        if rows3e2.b2d3e(list(E), sites={off})[0]!=tgt: NEG.add((E,off))
    for off,_,_ in rows3e2.b2d3e(list(A))[1]:
        if bE!=tuple(expand(rows3e2.b2d3e(list(A), sites={off})[0],m)): NEG.add((A,off))
print('壊れた %d 組 -> 負例 %d'%(len(br),len(NEG)))
pickle.dump(sorted(NEG), open('/tmp/h1work/h16neg_%s.pkl'%TAG,'wb'))
