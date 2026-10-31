"""WfT2R: is NotBumpKidX structural? Count, on standard M (t = 2), the columns i < x with the STRUCTURAL part of
BdX (e1,e2 != 0, m = P0 i = P1 i, CL_M i = [], i last counted child of m, no column upgrades to i) where m IS a bump
child of P0 m. A nonzero count means NotBumpKidX needs the value condition (not AbsAt)."""
import sys,pickle,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tools'); sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfAbsW')
from probe_inv3_prefix import Ctx
from probe_fail import mt
def one(M):
    cnt=collections.Counter(); ex=None
    if len(M)<3 or M[-1][2]==0: return cnt,ex
    C=Ctx(M)
    if not C.ok: return cnt,ex
    x=len(M)-1; E=C.e
    for i in range(x):
        if not C.e12(i): continue
        m=E.par(0,i)
        if m is None or E.par(1,i)!=m: continue
        clm=C.CL(m)
        if not (C.CL(i)==[] and clm and clm[-1]==i and all(C.upg(j)!=i for j in range(len(M)))): continue
        pm=E.par(0,m)
        bk=(pm is not None and M[m]==E.bump(pm))
        cnt['shape bumpKid=%s'%bk]+=1
        if bk and ex is None: ex=(mt(M),i)
    return cnt,ex
if __name__=='__main__':
    c=collections.Counter(); e=None
    for f in sys.argv[1:]:
        for M in pickle.load(open(f,'rb')):
            try: c1,e1=one([tuple(t) for t in M])
            except RecursionError: continue
            c.update(c1)
            if e is None and e1: e=e1
        print(f,dict(c)); sys.stdout.flush()
    print('EX',e)
