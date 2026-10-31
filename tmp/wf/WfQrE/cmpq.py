"""True values of N = M[n] (n = 2..nmax) on D columns i < x vs DQ(value_M(i), gamS(n - 2 + d_i)). (WfQrE)
usage: python3 cmpq.py MATRIX [nmax]   or import check(M, nmax) -> Counter"""
import sys,re,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQrE')
import trio
from dq import dq
from probe_adn import gamS, dependencies, lift_counts, Ctx, Z, fsD, lt
from ytosk_eval import tstr
def check(M,nmax=3,verbose=False):
    cnt=collections.Counter();ex=[]
    C=Ctx(M);x=len(M)-1;r=C.e.par(1,x);T=Ctx(M[:x])
    A=C.o(r);mu,br,_=A;seed=T.o(r);D=dependencies(C,x);d=lift_counts(C,x,A)
    for n in range(2,nmax+1):
        m=n-2
        N=[tuple(c) for c in trio.expand([list(c) for c in M],n)];CN=Ctx(N)
        if not CN.ok:cnt['Nevalfail']+=1;continue
        for i in range(x):
            for tag in (True,False):
                if (tag,i) not in D:continue
                t=C.o(i) if tag else C.v(i);tN=CN.o(i) if tag else CN.v(i)
                k=m+d[i];eta=gamS(mu,br,seed,k)
                if tN==t:cnt['same']+=1;continue
                if tN==fsD(t,eta):cnt['fsD.m%d'%min(m,2)]+=1;continue
                res=dq(t,tN,eta)
                sw=lt(tN,fsD(t,gamS(mu,br,seed,k+1))) and lt(fsD(t,eta),tN)
                cnt['sandwich%d'%int(sw)]+=1
                if res is None:
                    cnt['FAIL.m%d'%min(m,2)]+=1;ex.append(('FAIL',n,tag,i))
                else:
                    cnt['DQ.m%d'%min(m,2)]+=1;cnt['DQlevels%d'%len(res)]+=1
                    cnt['DQdepth'+','.join(str(dd) for dd,_ in res)]+=1
                if verbose:print('n',n,'o' if tag else 'v',i,'d',d[i],'res',None if res is None else [(dd,[tstr(q) for q in Q]) for dd,Q in res],'sandwich',sw,'\n   M:',tstr(t),'\n   N:',tstr(tN))
    return cnt,ex
if __name__=='__main__':
    M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',sys.argv[1])]
    c,e=check(M,int(sys.argv[2]) if len(sys.argv)>2 else 3,True);print(dict(c),e)
