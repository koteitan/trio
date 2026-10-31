"""WfT2X: at every column i < x (t = 2, n = 2, 3) where AbsAt fails: the full BadAbsShape and
NotBumpKid: m = P0 i is not a bump child of its parent (col m != bump(P0 m)); also directly that i is not a child of
any bump child j of a bump-type column (the engine's use)."""
import sys,pickle,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tools'); sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfAbsW')
from multiprocessing import Pool
from probe_inv3_prefix import Ctx,Z,lt,le,summ
import trio
from lhd_exact import lhd
from probe_fail import mt
W2=(Z,(Z,Z,(Z,Z,Z)),Z)
def one(M):
    cnt=collections.Counter(); ex={}
    if len(M)<3 or M[-1][2]==0: return cnt,ex
    C=Ctx(M)
    if not C.ok: return cnt,ex
    x=len(M)-1; E=C.e
    for n in (2,3):
        N=trio.expand(M,n); CN=Ctx(N)
        if not CN.ok: continue
        cnt['pairs']+=1
        for i in range(x):
            if not C.e12(i): continue
            p1=E.par(1,i); V=C.v(p1) if p1 is not None else Z
            WM=C.bumpW(i); WN=CN.bumpW(i)
            ok=all(lt(q,W2) or lt(q,WN) or not lt(q,WM) or lhd(q,WM) for q in summ(V))
            if ok: cnt['abs.ok']+=1; continue
            m=E.par(0,i)
            sh=(m is not None and m==p1)
            if sh:
                clm=C.CL(m); cln=CN.CL(m)
                sh=(C.CL(i)==[] and CN.CL(i)==[] and clm==cln and clm and clm[-1]==i
                    and all(C.o(d)==CN.o(d) for d in clm[:-1]) and C.v(m)==CN.v(m)
                    and all(C.upg(j)!=i for j in range(len(M))))
            pm=E.par(0,m) if m is not None else None
            nbk=not (pm is not None and M[m]==E.bump(pm))
            direct=not any(C.e12(ip) and M[m]==E.bump(ip) for ip in [pm] if ip is not None)
            key='absfail shape=%s notBumpKid=%s direct=%s'%(sh,nbk,direct)
            cnt[key]+=1; ex.setdefault(key,(mt(M),n,i))
    return cnt,ex
def run(b):
    c=collections.Counter(); e={}
    for M in b:
        try: c1,e1=one([tuple(t) for t in M])
        except RecursionError: c['rec']+=1; continue
        c.update(c1)
        for k,v in e1.items(): e.setdefault(k,v)
    return c,e
if __name__=='__main__':
    d=[m for m in pickle.load(open(sys.argv[1],'rb')) if len(m)>=3 and m[-1][2]!=0]
    np=3; B=[d[k::np*8] for k in range(np*8)]
    c=collections.Counter(); e={}
    with Pool(np) as P:
        for c1,e1 in P.imap_unordered(run,B):
            c.update(c1)
            for k,v in e1.items(): e.setdefault(k,v)
    print(sys.argv[1],len(d))
    for k,v in sorted(c.items()): print(' ',v,k)
    for k,v in e.items(): print('EX',k,str(v)[:300])
