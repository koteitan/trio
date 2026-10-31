import sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQnE')
import analyze as A
from analyze import *
def show(M,ns=(2,3)):
    C,x,r=A.frame(M); T=Ctx(M[:x]); seed=T.o(r); mu,b,_=C.o(r); D=dependencies(C,x)
    print('x',x,'r',r,'q',C.e.par(0,x),'o(r)',ts(C.o(r)),'seed',ts(seed))
    for n in ns:
        E=[tuple(c) for c in trio.expand([list(c) for c in M],n)]; CE=Ctx(E); zeta=gamS(mu,b,seed,n-2)
        for i in range(x):
            if (False,i) in D and fsD(C.v(i),zeta)!=CE.v(i):
                print('n',n,'i',i,M[i],'P0',C.e.par(0,i),'P1',C.e.par(1,i),'upg',C.upg(i),'e12',C.e12(i),'bad',bad_shape(C,i),'CL',C.CL(i),'ch',C.ch(i))
                print('   vM',ts(C.v(i)),'\n   glue',ts(fsD(C.v(i),zeta)),'\n   true',ts(CE.v(i)))
                if C.e12(i): print('   W',ts(C.bumpW(i)),' V',ts(C.vOpt1(i)))
M=[tuple(map(int,t)) for t in __import__('re').findall(r'\((\d+),(\d+),(\d+)\)',sys.argv[1])]
show(M)
