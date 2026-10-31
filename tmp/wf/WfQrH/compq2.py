"""WfQrH6 fields (DQC) on true values of M[n], n = 2..NMAX, q = r frames (as tmp/wf/WfQrL/compq.py):
 C_strip : new components g in comps(a, bN) \\ comps(a, bS) are < bS   (bS = bN with every Q removed)
 OT_S    : isOT(psi_a(bS)) at every argument level (the stripped value is standard)   [new]
 OT_Q    : isOT(Q) for every re-exposed Q                                              [new]
 DQ      : a DQ decomposition exists (DQFAIL counts failures)
usage: nice -n 15 python3 compq2.py NPROC NMAX OUT.jsonl PKL..."""
import sys,os,pickle,json,collections,time
from multiprocessing import Pool
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvA');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQrL')
import trio
from probe_inv3_prefix import Z, lt, comps, isOT
from probe_adn import gamS, dependencies, lift_counts, Ctx, ms
from compq import dq, mk
NMAX=3
def check(M,cnt,ex):
    def note(f,ok,key):
        cnt[f+('.ok' if ok else '.FAIL')]+=1
        if not ok and (f not in ex or key[0]<ex[f][0]):ex[f]=key
    x=len(M)-1
    if x<1 or M[x][1]==0 or M[x][2]!=0:return
    C=Ctx(M)
    if not C.ok:return
    r=C.e.par(1,x)
    if r is None or C.e.par(0,x)!=r:return
    T=Ctx(M[:x]);A=C.o(r);mu,br,_=A;seed=T.o(r);D=dependencies(C,x);d=lift_counts(C,x,A)
    cnt['frames']+=1
    for n in range(2,NMAX+1):
        N=[tuple(c) for c in trio.expand([list(c) for c in M],n)];CN=Ctx(N)
        if not CN.ok:cnt['Nevalfail']+=1;continue
        for i in range(x):
            for tag in (True,False):
                if (tag,i) not in D:continue
                t=C.o(i) if tag else C.v(i);tN=CN.o(i) if tag else CN.v(i)
                if tN==t:continue
                key=(len(M),ms(M),n,tag,i)
                res=dq(t,tN,gamS(mu,br,seed,n-2+d[i]))
                if res is None:note('DQ',False,key);continue
                cnt['DQ.ok']+=1
                for e in res[1]:
                    if e[0]=='Q':note('OT_Q',isOT(mk(e[2])),key)
                    elif e[0]=='arg':
                        _,dp,a,bN,bS=e
                        note('OT_S',isOT((a,bS,Z)),key)
                        old=set(comps(a,bS))
                        note('C_strip',all(lt(g,bS) for g in comps(a,bN) if g not in old),key)
def work(batch):
    cnt=collections.Counter();ex={}
    for mm in batch:
        M=[tuple(c) for c in mm]
        try:check(M,cnt,ex);cnt['mats']+=1
        except Exception as e:
            cnt['exc.'+type(e).__name__]+=1;ex.setdefault('exc',(len(M),ms(M),repr(e)[:200]))
    return cnt,ex
if __name__=='__main__':
    npr=int(sys.argv[1]);NMAX=int(sys.argv[2]);out=open(sys.argv[3],'a')
    for f in sys.argv[4:]:
        t=time.time();mats=pickle.load(open(f,'rb'))
        CAP=int(os.environ.get('CAP','0'))
        if CAP and len(mats)>CAP:
            import random;random.seed(1);mats=random.sample(list(mats),CAP)
        cnt=collections.Counter();ex={}
        with Pool(npr,initializer=globals().__setitem__,initargs=('NMAX',NMAX)) as pool:
            for c,e in pool.imap_unordered(work,(mats[i:i+50] for i in range(0,len(mats),50))):
                cnt.update(c)
                for k,v in e.items():
                    if k not in ex or v[0]<ex[k][0]:ex[k]=v
        out.write(json.dumps({'set':os.path.basename(f),'n':len(mats),'sec':round(time.time()-t),'cnt':dict(sorted(cnt.items())),'ex':ex},default=str)+'\n');out.flush()
