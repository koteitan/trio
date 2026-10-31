"""Graft round 3 around the bad frames (t = 1, q != r): seeds = matrices of graftQ2 with a bad call (sample),
ops of WfQnE/graft.py (grow).  usage: nice -n 15 python3 graftQ3.py OUT.pkl NSEED NPROC"""
import sys,pickle,random
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQnE');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvA')
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import graft as GR
import analyze as A
from probe_inv3_prefix import Ctx, lt, summ, fsD
from probe_inv2 import dependencies
from multiprocessing import Pool
def hasbad(M):
    try:
        f=A.frame(list(M))
        if f is None: return False
        C,x,r=f
        T=Ctx(list(M)[:x])
        if not T.ok: return False
        seed=T.o(r); mu,b,_=C.o(r); A_=C.o(r)
        D=dependencies(C,x)
        for i in range(x):
            if (False,i) in D and C.e12(i) and A.bad_shape(C,i) and C.bumpW(i)==A_:
                for n in (2,3):
                    Az=fsD(A_,A.gamS(mu,b,seed,n-2))
                    if any(lt(q,A_) and not lt(q,Az) for q in summ(C.vOpt1(i))): return True
        return False
    except Exception: return False
if __name__=='__main__':
    out,ns,npr=sys.argv[1],int(sys.argv[2]),int(sys.argv[3])
    S=[tuple(tuple(c) for c in M) for M in pickle.load(open('/home/koteitan/proofs/trio/tmp/wf/WfQnE/graftQ2.pkl','rb'))]
    random.seed(11);random.shuffle(S)
    with Pool(npr) as p:
        seeds=[M for M,h in zip(S[:ns*4],p.map(hasbad,S[:ns*4],chunksize=20)) if h][:ns]
        print('seeds',len(seeds),flush=True)
        allg=set()
        for g in p.imap_unordered(GR.grow,seeds,chunksize=1): allg|=g
    allg-=set(S)
    allg=sorted(allg,key=lambda N:(len(N),N))
    pickle.dump(allg,open(out,'wb'));print('grafts',len(allg),flush=True)
