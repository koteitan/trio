"""WfSdP: what the weak seed of t = 1, q = r satisfies (2026-11-01).
Weak case: seed = o'(r) (M.take x) = Om_{w'} not lhd o(r). Measures
 wcs2mu : WCS2(mu, w')  (mu = v(r))  -> SeedOK mu br mu seed and gamma_1 lhd o(r) (Lean: lhd_weak_childA)
 wcs2p0 : CS w' or WCS2(v(P0 r), w')  (PV2 at r)
 w=V+1  : w' = V + 1, V = v(P1 r);  rx1: r = x - 1;  p01: P0 r = P1 r
 muapp  : mu = V + last(v(upg r)) syntactically (no absorption by sf)
 domV   : forall u <= mu, g in comps u V: exists d in comps u mu, g <= d
usage: nice -n 15 python3 seedp.py NPROC PKL..."""
import sys,os,json,collections,time
from multiprocessing import Pool
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.append('/home/koteitan/proofs/trio/tmp/codex')
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvD');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfDrE')
from probe_inv3_prefix import Ctx,Z,ONE,lt,le,isOT,succ
from lhd_exact import lhd,lhdE,comps
import probe_dropres as D
import invd
from pv2 import load,WCS2
SRO=invd.SRO;ms=invd.ms
def app(b,t):return t if not b else (b[0],b[1],app(b[2],t))
def lastS(y):
    while y[2]:y=y[2]
    return (y[0],y[1],Z)
def CS(w):
    return all(lt(g,(ONE,Z,Z)) for g in comps(Z,w))
def domV(V,mu):
    for u in D.levels(mu,V):
        if lt(mu,u):continue
        mx=D.tmax(comps(u,mu))
        for g in comps(u,V):
            if not le(g,mx):return False
    return True
def probe(M):
    M=[tuple(c) for c in M];cnt=collections.Counter();ex={}
    if not M<SRO or len(M)<3:return cnt,ex
    x=len(M)-1
    if not(M[x][1] and not M[x][2]):return cnt,ex
    C=Ctx(M)
    if not C.ok:return cnt,ex
    p0x=C.e.par(0,x)
    if p0x is None or C.e.par(1,x)!=p0x:return cnt,ex
    T=Ctx(M[:-1])
    if not T.ok:cnt['evalfail']+=1;return cnt,ex
    def X(tag,info=''):
        cnt[tag]+=1
        if tag not in ex or len(M)<ex[tag][0]:ex[tag]=(len(M),ms(M),str(info)[:300])
    r=p0x;seed=T.o(r);o=C.o(r);mu=C.v(r)
    cnt['cases']+=1
    if lhd(seed,o):cnt['lhd']+=1;return cnt,ex
    weak=seed[1]==Z and seed[2]==Z and lt(seed[0],mu)
    if not weak:X('notlhd.notweak');return cnt,ex
    w=seed[0]
    p0=C.e.par(0,r);p1=C.e.par(1,r)
    V=C.v(p1) if p1 is not None else Z
    Vp0=C.v(p0) if p0 is not None else Z
    k=C.e.upg(r) if hasattr(C.e,'upg') else None
    a=WCS2(mu,w);b=CS(w) or WCS2(Vp0,w)
    X('weak.wcs2mu=%d.pv2=%d'%(a,b))
    X('weak.w=V+1=%d.rx1=%d.p01=%d'%(w==app(V,ONE),r==x-1,p0==p1))
    X('weak.domV=%d'%domV(V,mu))
    X('weak.wcs2p0=%d.cs=%d'%(WCS2(Vp0,w),CS(w)))
    return cnt,ex
def work(bt):
    cnt=collections.Counter();ex={}
    for M in bt:
        try:c,e=probe(M)
        except Exception as er:
            c=collections.Counter({'exc.'+type(er).__name__:1});e={'exc':(len(M),ms(M),repr(er)[:200])}
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
