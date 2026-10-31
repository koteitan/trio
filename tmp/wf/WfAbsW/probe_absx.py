"""AbsWNx M M[n] (n = 2, 3) for t = 2: at every i < x with e1, e2 != 0, AbsWN at i or the bad shape
BadAbsShape (P0 i = P1 i = m, CL_M i = CL_N i = [], CL_M m = CL_N m = Lc ++ [i], o unchanged on Lc, v(m) unchanged,
no upg into i). Also: where AbsWN fails, does Lhd_{v(P1 i)} hold for v(i), o(i), and Lhd z for o(m)."""
import sys,pickle,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tools'); sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfAbsW')
from multiprocessing import Pool
from probe_inv3_prefix import Ctx,Z,lt,le,summ
import trio
from lhd_exact import lhd
from probe_fail import lhd_eta, mt
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
            sh=dict(P0eqP1=(m==p1 and m is not None))
            if sh['P0eqP1']:
                clm=C.CL(m); cln=CN.CL(m)
                sh['CLi']=(C.CL(i)==[] and CN.CL(i)==[])
                sh['last']=(clm==cln and clm and clm[-1]==i and all(C.o(d)==CN.o(d) for d in clm[:-1]))
                sh['vm']=(C.v(m)==CN.v(m))
                sh['noupg']=all(C.upg(j)!=i for j in range(len(M)))
            shape=all(sh.values())
            vl=lhd(CN.v(i),C.v(i)) if CN.v(i)!=C.v(i) else 'eq'
            key='absfail shape=%s %s vLhdz=%s vLhdV=%s oLhdV=%s om=%s'%(shape,
                ','.join(k for k,v in sh.items() if not v),vl,
                lhd_eta(CN.v(i),C.v(i),V) if CN.v(i)!=C.v(i) else 'eq',
                lhd_eta(CN.o(i),C.o(i),V) if CN.o(i)!=C.o(i) else 'eq',
                (lhd(CN.o(m),C.o(m)) if CN.o(m)!=C.o(m) else 'eq') if m is not None else '-')
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
    np=4; B=[d[k::np*8] for k in range(np*8)]
    c=collections.Counter(); e={}
    with Pool(np) as P:
        for c1,e1 in P.imap_unordered(run,B):
            c.update(c1)
            for k,v in e1.items(): e.setdefault(k,v)
    print(sys.argv[1],len(d))
    for k,v in sorted(c.items()): print(' ',v,k)
    for k,v in e.items(): print('EX',k,v)
