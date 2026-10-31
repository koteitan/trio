"""Compare true values of N = M[n] on columns i < x of D with fsD(value_M(i), gamS(k)) (WfQrE).
usage: python3 cmp.py MATRIX [nmax]"""
import sys,re
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvA')
import trio
from probe_adn import gamS, dependencies, lift_counts, Ctx, Z, fsD, summ, lt, ohole, cof
from ytosk_eval import tstr
def matchk(t,tN,mu,br,seed,K=8):
    if t==tN:return 'same'
    if not ohole(t):return None
    for k in range(K):
        if fsD(t,gamS(mu,br,seed,k))==tN:return k
    return None
if __name__=='__main__':
    s=sys.argv[1];nmax=int(sys.argv[2]) if len(sys.argv)>2 else 3
    M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',s)]
    C=Ctx(M);x=len(M)-1;r=C.e.par(1,x);T=Ctx(M[:x])
    A=C.o(r);mu,br,_=A;seed=T.o(r);D=dependencies(C,x);d=lift_counts(C,x,A)
    print('x',x,'r',r,'A',tstr(A),'seed',tstr(seed))
    for n in range(2,nmax+1):
        N=[tuple(c) for c in trio.expand([list(c) for c in M],n)];CN=Ctx(N)
        print('== n',n,'N len',len(N))
        for i in range(x):
            for tag in (True,False):
                if (tag,i) not in D:continue
                t=C.o(i) if tag else C.v(i);tN=CN.o(i) if tag else CN.v(i)
                k=matchk(t,tN,mu,br,seed)
                print(' ','o' if tag else 'v',i,M[i],'d',d.get(i),'k',k,'' if k is not None else ' M:'+tstr(t)+'  N:'+tstr(tN))
