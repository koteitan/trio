import sys, os, pickle
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
import rows3, rows3k2
from core import expand
TAG=os.environ['TAG']
b0=pickle.load(open('/tmp/h1work/ag_v18_7.pkl','rb'))
s0=pickle.load(open('/tmp/h1work/ag_%s_7.pkl'%TAG,'rb'))
br=sorted(b0-s0, key=lambda e:(len(e[0]),e)); new=sorted(s0-b0, key=lambda e:(len(e[0]),e))
NEG,POS=set(),set()
for pairs,dest in ((br,NEG),(new,POS)):
    for A,n,m in pairs:
        E=tuple(tuple(x) for x in expand(A,n))
        bA=rows3k2.b2d3k(list(A), sites=set())[0]; bE=rows3k2.b2d3k(list(E), sites=set())[0]
        tgt=tuple(expand(bA,m))
        for off,_,_ in rows3k2.b2d3k(list(E))[1]:
            if (rows3k2.b2d3k(list(E), sites={off})[0]!=tgt)==(dest is NEG): dest.add((E,off))
        for off,_,_ in rows3k2.b2d3k(list(A))[1]:
            if (bE!=tuple(expand(rows3k2.b2d3k(list(A), sites={off})[0],m)))==(dest is NEG): dest.add((A,off))
print('壊れた %d 組 -> 負例 %d / 新しく一致 %d 組 -> 正例 %d'%(len(br),len(NEG),len(new),len(POS)))
pickle.dump(sorted(NEG), open('/tmp/h1work/h17neg_%s.pkl'%TAG,'wb'))
pickle.dump(sorted(POS), open('/tmp/h1work/h17pos_%s.pkl'%TAG,'wb'))
