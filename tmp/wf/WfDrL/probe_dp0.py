"""WfDrL (3): the index-0 obligation of hok_of_seedC2 (2026-10-31).
Frame: t = 1, q = r (P0 x = P1 x = r), o(r) = psi_mu(b_r), b_r = b + Om_{mu+1}. seed = o_{M.take x}(r).
For every column i < x in D (o or v call) with lift count d[i] = 0 (dOf, tools/probe_trigs0.lift_counts), the
diagonal points a' <= mu (DiagAt a' b_r mu t, seedc.diag) of t = o(i) (if (True,i) in D) and t = v(i) (if (False,i)
in D) must all be mu.  Counted separately for the weak seed (SeedC2 weak branch: seed = Om_{w'}, w' < mu, not lhd o(r)).
Also: DPz = same for all columns (any d), to see whether d = 0 matters.
usage: nice -n 15 python3 probe_dp0.py NPROC PKL..."""
import sys,os,json,collections,time
from multiprocessing import Pool
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.append('/home/koteitan/proofs/trio/tmp/codex')
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvD');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfDrE')
from probe_inv3_prefix import Ctx,Z,ONE,lt,succ,last
from lhd_exact import lhd
from probe_inv2 import dependencies
from probe_trigs0 import lift_counts
import ytosk_eval as Y
from seedc import diag
from pv2 import load
import invd
def probe(M):
    M=[tuple(c) for c in M];cnt=collections.Counter();ex={}
    if not M<invd.SRO or len(M)<3:return cnt,ex
    x=len(M)-1
    if not(M[x][1] and not M[x][2]):return cnt,ex
    C=Ctx(M)
    if not C.ok:return cnt,ex
    r=C.e.par(0,x)
    if r is None or C.e.par(1,x)!=r:return cnt,ex
    A=C.o(r);mu,br,rest=A
    if rest!=Z or not br or last(br)!=(succ(mu),Z,Z):return cnt,ex
    T=Ctx(M[:x])
    if not T.ok:cnt['evalfail']+=1;return cnt,ex
    seed=T.o(r)
    weak=not lhd(seed,A) and seed[1]==Z and seed[2]==Z and lt(seed[0],mu)
    tag='weak' if weak else ('lhd' if lhd(seed,A) else 'other')
    cnt['frames.'+tag]+=1
    D=dependencies(C,x);d=lift_counts(C,x,A)
    def X(k,info):
        cnt[k]+=1
        if k not in ex or len(M)<ex[k][0]:ex[k]=(len(M),invd.ms(M),str(info)[:300])
    for i in range(x):
        for role,t in ((True,C.o(i)),(False,C.v(i))):
            if (role,i) not in D:continue
            s=set();diag(t,br,mu,s)
            bad=[a for a in s if a!=mu]
            k='d0' if d[i]==0 else 'dpos'
            cnt['%s.%s.cases'%(tag,k)]+=1
            if bad:X('%s.%s.FAIL.%s'%(tag,k,'o' if role else 'v'),(i,M[i],d[i],[Y.tstr(a)[:60] for a in bad]))
    return cnt,ex
def work(b):
    cnt=collections.Counter();ex={}
    for M in b:
        try:c,e=probe(M)
        except Exception as er:c=collections.Counter({'exc.'+type(er).__name__:1});e={'exc':(len(M),invd.ms(M),repr(er)[:200])}
        cnt.update(c)
        for k,v in e.items():
            if k not in ex or v[0]<ex[k][0]:ex[k]=v
    return cnt,ex
if __name__=='__main__':
    npr=int(sys.argv[1]);lim=int(os.environ.get('LIMIT','0'))
    for f in sys.argv[2:]:
        t0=time.time();mats=load(f)
        if lim and len(mats)>lim:
            import random;random.seed(5);mats=random.sample(mats,lim)
        cnt=collections.Counter();ex={}
        with Pool(npr) as p:
            for c,e in p.imap_unordered(work,(mats[i:i+50] for i in range(0,len(mats),50))):
                cnt.update(c)
                for k,v in e.items():
                    if k not in ex or v[0]<ex[k][0]:ex[k]=v
        print(json.dumps({'set':f.split('/')[-1],'n':len(mats),'sec':round(time.time()-t0),'cnt':dict(sorted(cnt.items())),'ex':ex}),flush=True)
