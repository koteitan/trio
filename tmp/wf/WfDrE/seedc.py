"""WfDrE: replacement of the t = 1, q = r seed condition SeedC (2026-10-31).
Case: t = 1 (e1 x != 0, e2 x = 0), P0 x = P1 x = r. seed = o'(r) (M.take x), mu = v(r), o(r) = psi_mu(b + Om_{mu+1}), br = b + Om_{mu+1}.
Consumer: hS (V3QRFinal3 qr_final3): SeedOK a' br mu seed for the a' it is applied to. Those are a' = mu (hok_of_holeT hSr)
and the diagonal points of HoleT (DiagAt a' br mu t: the node psi_{a'}(br) on the last-term path of t). We collect
DP = {a' <= mu : DiagAt a' br mu t for t = o(i) or v(i), i < x} u {mu}.
SeedOK a' br mu seed (FSS.lean) with fs br seed = b + seed:
  ot, lt_om (seed < Om_{mu+1}), lt_next (seed < psi_mu(b + seed)), comps_a (g in comps a' seed -> g < b + seed),
  dom: forall u <= a', c0 in (b + seed, br], c1: comps u seed dominated by comps u (psi_{a'}(c0) + c1) ++ [0].
  Checked here in the sufficient form domS: g <= b + seed  or  g <= some d in comps u a'  (c0 > b + seed is in the list).
Forms:
  old  : seed lhd o(r)  or  (seed = Om_{w'}, w' < mu, SmallSelf w')
  SCA  : seed lhd o(r)  or  (seed = Om_{w'}, w' < mu, forall a' in DP: ot, lt_om, lt_next, comps_a, domS)   [restricted to DP]
  SCB  : seed lhd o(r)  or  (weak, SeedOK(seed) at DP of the bad part i >= r and at mu, SeedOK(gamS 1 = psi_mu(b + seed)) at DP of i < r)
  SC2  : seed lhd o(r)  or  (weak, SeedOK mu br mu seed, gamS 1 = psi_mu(b + seed) lhd o(r))   [Lean: WfDrE2.SeedC2]
  G1   : SeedOK(gamS 1) at every DP point
  SCG  : seed lhd o(r)  or  (seed = Om_{w'}, w' < mu, forall g in comps 0 w': g < b + seed)  [all a'; implies SeedOK for every a']
usage: nice -n 15 python3 seedc.py NPROC PKL..."""
import sys,os,pickle,json,collections,time
from multiprocessing import Pool
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.append('/home/koteitan/proofs/trio/tmp/codex')
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvD');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfDrE')
from probe_inv3_prefix import Ctx,Z,ONE,lt,le,isOT,succ
from lhd_exact import lhd,lhdE,comps
import probe_dropres as D
import ytosk_eval as Y
import invd
from pv2 import load
SRO=invd.SRO;ms=invd.ms
def app(b,t):return t if not b else (b[0],b[1],app(b[2],t))
def strip_last(y):
    if not y or not y[2]:return Z
    return (y[0],y[1],strip_last(y[2]))
def lastS(y):
    while y[2]:y=y[2]
    return (y[0],y[1],Z)
def isSucc(t):
    while t and t[2]:t=t[2]
    return t==ONE
def diag(t,br,mu,out):
    if not t:return
    a,b,c=t
    if c:diag(c,br,mu,out);return
    if b==br and not lt(mu,a):out.add(a)
    if b:
        if not isSucc(b):diag(b,br,mu,out)
    elif a and not isSucc(a):diag(a,br,mu,out)
def seedok(ap,b,mu,seed):
    bs=app(b,seed);ok={}
    ok['ot']=isOT(seed);ok['lt_om']=lt(seed,(succ(mu),Z,Z));ok['lt_next']=lt(seed,(mu,bs,Z))
    ok['comps_a']=all(lt(g,bs) for g in comps(ap,seed))
    dm=True
    for u in D.levels(ap,seed):
        mx=D.tmax(comps(u,ap))
        for g in comps(u,seed):
            if not(le(g,bs) or le(g,mx)):dm=False;break
        if not dm:break
    ok['domS']=dm
    return ok
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
    if o[0]!=mu or not o[1] or lastS(o[1])!=(succ(mu),Z,Z):X('shape.o_r.unexpected');return cnt,ex
    b=strip_last(o[1]);br=o[1]
    L=lhd(seed,o)
    if L:cnt['lhd']+=1;return cnt,ex
    weak=seed[1]==Z and seed[2]==Z and lt(seed[0],mu)
    w=seed[0]
    small=weak and all(lt(g,(w,Z,Z)) for g in comps(Z,w))
    bs=app(b,seed)
    scg=weak and all(lt(g,bs) for g in comps(Z,w))
    DP={mu};DPg=set()
    for i in range(x):
        tgt=DP if i>=r else DPg
        diag(C.o(i),br,mu,tgt);diag(C.v(i),br,mu,tgt)
    g1=(mu,app(b,seed),Z)
    scb=weak and all(all(seedok(ap,b,mu,seed).values()) for ap in DP) and all(all(seedok(ap,b,mu,g1).values()) for ap in DPg)
    allg1=all(all(seedok(ap,b,mu,g1).values()) for ap in DP|DPg)
    l1=lhd(g1,o)
    s0=all(seedok(mu,b,mu,seed).values())
    DPall=DP|DPg
    cnt['DP.size.%d'%min(len(DP),9)]+=1
    sca=weak
    bad=[]
    if weak:
        for ap in DPall:
            ok=seedok(ap,b,mu,seed)
            for k,v in ok.items():
                if not v:bad.append(k);sca=False
    key='notlhd.weak=%d.old=%d.SCA=%d.SCG=%d.SCB=%d.G1=%d'%(weak,small,sca,scg,scb,allg1)
    X('SC2.weak=%d.seedOKmu=%d.g1lhd=%d'%(weak,s0,l1),r)
    X(key,(r,sorted(set(bad))))
    for k in set(bad):cnt['SCA.fieldfail.'+k]+=1
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
