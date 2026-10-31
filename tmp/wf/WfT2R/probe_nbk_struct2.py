"""Which structural part of BdX fails when m = P0 i is a bump child: counts of (P1 i = m, counted, last counted,
CL i = [], upg to i) over children i (e1, e2 != 0) of bump children m."""
import sys,pickle,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tools'); sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfAbsW')
from probe_inv3_prefix import Ctx
from probe_fail import mt
c=collections.Counter(); ex={}
for f in sys.argv[1:]:
    for M in pickle.load(open(f,'rb')):
        M=[tuple(t) for t in M]
        if len(M)<3 or M[-1][2]==0: continue
        try:
            C=Ctx(M)
            if not C.ok: continue
            E=C.e; x=len(M)-1
            for i in range(x):
                if not C.e12(i): continue
                m=E.par(0,i)
                if m is None: continue
                pm=E.par(0,m)
                if pm is None or M[m]!=E.bump(pm): continue
                clm=C.CL(m)
                k=(E.par(1,i)==m, i in clm, bool(clm) and clm[-1]==i, C.CL(i)==[], all(C.upg(j)!=i for j in range(len(M))))
                c[k]+=1; ex.setdefault(k,(mt(M),i))
        except RecursionError: continue
    print(f); 
for k,v in sorted(c.items()): print(v,'P1=m,counted,last,CLnil,noupg=',k, str(ex[k])[:200])
