import sys,re
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQnA')
from meas import *
def show(s,n=2):
    M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',s)]
    C,x,r=A.frame(M); T=Ctx(M[:x]); seed=T.o(r); mu,b,_=C.o(r); A_=C.o(r)
    D=dependencies(C,x)
    cand=[i for i in range(x) if (False,i) in D and C.e12(i) and A.bad_shape(C,i) and C.bumpW(i)==A_]
    zeta=A.gamS(mu,b,seed,n-2); Az=fsD(A_,zeta)
    B=[i for i in cand if any(lt(q,A_) and not lt(q,Az) for q in summ(C.vOpt1(i)))]
    DB=A.closure(C,{(False,i) for i in B},x)
    print('len',len(M),'x',x,'r',r,'B',B,'r in DB',(True,r) in DB)
    print('DB',sorted(DB))
    for i in B:
        m=C.e.par(0,i); print('bad',i,'m=P0=P1',m,'col',M[i],'col m',M[m],'children',C.ch(i))
    for j in range(min(B+[r])-3 if B else 0,x+1):
        print(j,M[j],'p0',C.e.par(0,j),'p1',C.e.par(1,j),'inD',[(b,jj) for (b,jj) in D if jj==j])
show(sys.argv[1],int(sys.argv[2]) if len(sys.argv)>2 else 2)
