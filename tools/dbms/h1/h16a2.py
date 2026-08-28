import sys, time
sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
import rows3, imgfast
from core import expand, show
CAP=60000
LAD=((4,CAP,False,None),(6,CAP,False,None),(8,CAP,False,None),(12,CAP,False,None))
A=((0,0,0),(1,1,1),(1,1,0),(2,2,1),(2,1,0))
fA=tuple(map(tuple,rows3.b2d3(list(A))))
print('A2 = %s  conv3 = %s'%(show(list(A)), show([list(x) for x in fA])))
for m in (3,4,5):
    T=tuple(expand(fA,m)); t0=time.time()
    _,B,st,nodes,capped=imgfast.find2(tuple(A),m,f=rows3.b2d3,ladder=LAD,T=T,scale=64)
    print('  m=%d |T|=%2d -> %s (段 %s, 節点 %d, 打ち切り %s, %.0fs)'
          %(m,len(T),('**逆像 %s**'%show([list(x) for x in B])) if B else 'なし',st,nodes,capped,time.time()-t0), flush=True)
