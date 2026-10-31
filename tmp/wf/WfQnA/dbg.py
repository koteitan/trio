import sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQnA')
from meas import *
import re
s=sys.argv[1]; n=int(sys.argv[2]); i0=int(sys.argv[3])
M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',s)]
C,x,r=A.frame(M); T=Ctx(M[:x]); seed=T.o(r); mu,b,_=C.o(r); A_=C.o(r)
D=dependencies(C,x)
cand=[i for i in range(x) if (False,i) in D and C.e12(i) and A.bad_shape(C,i) and C.bumpW(i)==A_]
zeta=A.gamS(mu,b,seed,n-2); Az=fsD(A_,zeta)
B=[i for i in cand if any(lt(q,A_) and not lt(q,Az) for q in summ(C.vOpt1(i)))]
DB=A.closure(C,{(False,i) for i in B},x)
print('x',x,'r',r,'B',B,'i0 in B',i0 in B)
W=C.bumpW(i0); print('W==A',W==A_)
for q in summ(C.vOpt1(i0)):
    if not lt(q,W2) and lt(q,W): print('q<Az',lt(q,Az),'lhd',LX.lhd(q,W))
