import sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from probe_inv3_prefix import Ctx, Z, ONE, fs, fsD, holelev, lt, summ, ohole, Y as YE
from probe_inv2 import dependencies
import trio
ts=YE.tstr
def gamS(mu,b,seed,k):
    g=seed
    for _ in range(k): g=(mu,fs(b,g),Z)
    return g
def run(M, ns=(2,3,4), show=True):
    C=Ctx(M); x=len(M)-1; r=C.e.par(1,x)
    T=Ctx(M[:x]); seed=T.o(r); mu,b,_=C.o(r)
    D=dependencies(C,x)
    out=[]
    for n in ns:
        E=[tuple(c) for c in trio.expand([list(c) for c in M],n)]
        CE=Ctx(E); zeta=gamS(mu,b,seed,n-2)
        for i in range(r):
            for kind,f,g in (('v',C.v,CE.v),('o',C.o,CE.o)):
                dep=(kind=='o',i) in D
                exp=fsD(f(i),zeta) if dep else f(i)
                if exp!=g(i):
                    out.append((n,i,kind,dep))
                    if show: print('n',n,'i',i,kind,'dep',dep,'\n   glue',ts(exp),'\n   true',ts(g(i)))
    return out
if __name__=='__main__':
    N=[(0,0,0),(1,1,1),(2,1,1),(3,1,0),(1,1,1),(2,1,1),(3,0,0),(4,1,1),(5,1,1),(6,0,0),(7,1,1),(8,1,1),(9,0,0),(10,1,1),(11,1,1),(11,1,0),(12,1,0),(13,0,0),(10,0,0),(2,1,0),(3,2,1),(4,2,1),(5,0,0),(6,1,1),(7,1,1),(8,1,0)]
    run(N,(2,3,4,5))
