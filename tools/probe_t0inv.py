import sys, os, pickle, random
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, os.path.expanduser('~/proofs/trio/tools'))
from probe_inv3_prefix import *
import trio
CP=os.environ.get('CPRIME', 'Cprime.pkl')  # C′（接頭辞で閉じた標準形の集合）の pickle
def lhdE(a,b): return a==b or lhd(a,b)
def cls(XN,XM,s):
    th=(succ(s),Z,Z)
    hN,lN=split(XN,th); hM,lM=split(XM,th)
    if XN==XM: return 'eq'
    if lN==Z and lM==Z: return 'B'
    if hN==hM and lN!=Z: return 'A'
    return 'other:%s,%s,%s'%('hsame' if hN==hM else ('hlt' if lt(hN,hM) else 'hgt'),'lN0' if lN==Z else 'lN+','lM0' if lM==Z else 'lM+')
def check(M):
    M=list(M); cnt=Counter(); ex={}
    def note(f, ok, info):
        cnt[(f,'cases')]+=1
        if not ok:
            cnt[(f,'FAIL')]+=1
            if len(ex.setdefault(f,[]))<3: ex[f].append((M,info))
    x=len(M)-1
    if x<1 or M[x][1]!=0 or M[x]==(0,0,0): return cnt,ex
    C=Ctx(M)
    if not C.ok: return cnt,ex
    r=C.e.par(0,x)
    for n in (2,3):
        N=trio.expand(M,n); CN=Ctx(N)
        if not CN.ok: cnt['noval']+=1; continue
        g=C.e.par(0,r)
        for i in range(r):
            if CN.o(i)==C.o(i): continue
            tag='g' if i==g else 'up'
            vN=CN.v(i); vM=C.v(i)
            if vN!=vM:
                cnt[('vchg',tag,CN.o(i)[1]==Z, C.o(i)[1]==Z)]+=1; continue
            c=cls(CN.o(i)[1],C.o(i)[1],vM)
            cnt[('cls',tag,c)]+=1
            if c.startswith('other'): note('other-'+tag,False,(n,i))
            # mixed trig at this node
            cl=CN.CL(i); clM=C.CL(i)
            cs=cl[-1]; BN=CN.pre(i,cl[:-1]); BM=C.pre(i,clM[:-1])
            sN,yN,_=CN.o(cs); sM,yM,_=C.o(clM[-1])
            tN=lt(BN,yN) and lt((vN,Z,Z),(sN,yN,Z)); tM=lt(BM,yM) and lt((vM,Z,Z),(sM,yM,Z))
            if tag=='up':
                cc=('vchgchild' if sN!=sM else cls(yN,yM,sM))
                cnt[("upchild",cc,tN,tM)]+=1
                if cc=="B" and tM: cnt[("Btrig B==0",BM==Z, "yN==0", yN==Z)]+=1
                if cc=="A": cnt[("A: B<=hi", True)]+=1
    return cnt,ex
if __name__=='__main__':
    mats=pickle.load(open(CP,'rb'))
    random.seed(int(sys.argv[2]) if len(sys.argv)>2 else 1)
    k=int(sys.argv[1]) if len(sys.argv)>1 else 20000
    mats=random.sample(mats,min(k,len(mats)))
    tot=Counter(); exs={}
    with Pool(8) as p:
        for c,e in p.imap_unordered(check,mats,chunksize=200):
            tot.update(c)
            for f,l in e.items():
                if len(exs.setdefault(f,[]))<3: exs[f]+=l
    for k_,v in sorted(tot.items(),key=str): print(k_,v)
    for f,l in exs.items():
        print(f)
        for m,info in l[:3]: print('  ',''.join('(%d,%d,%d)'%c for c in m),info)
