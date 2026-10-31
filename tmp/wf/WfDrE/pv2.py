"""WfDrE: the drop conclusion PV with the weak component condition WCS2 (2026-10-31).
WCS2 a w := forall u, not a < u -> forall g in comps u w, g <= psi w 0 0  or  exists d in comps u a, g <= d
(only what lhd_weak_childA needs; WCS has g < Om 1 in place of g <= psi w 0 0).
PV2 i := isOT v'(i) and (v' = v or v' lhdE v or (WkVA v' v and (CS v' or WCS2 v(P0 i) v') and CntX i)).
Counts per matrix (< SRO, len >= 3): weak cases (v' not lhdE v), PV fails, PV2 fails, and the reason of each PV2 failure.
usage: nice -n 15 python3 pv2.py NPROC PKL...   (prints one json line per pkl)"""
import sys,os,pickle,json,collections,time
from multiprocessing import Pool
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.append('/home/koteitan/proofs/trio/tmp/codex')
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvD')
from probe_inv3_prefix import Ctx,Z,ONE,lt,le,isOT
from lhd_exact import lhd,lhdE,comps
import probe_dropres as D
import ytosk_eval as Y
import invd
SRO=invd.SRO;ms=invd.ms
def WCS2(a,w):
    W=(w,Z,Z)
    for u in D.levels(a,w):
        mx=D.tmax(comps(u,a))
        for g in comps(u,w):
            if not (le(g,W) or le(g,mx)):return False
    return True
def probe(M):
    M=[tuple(c) for c in M];cnt=collections.Counter();ex={}
    if not M<SRO or len(M)<3:return cnt,ex
    C=Ctx(M);T=Ctx(M[:-1]);x=len(M)-1;n=len(M)
    if not(C.ok and T.ok):cnt['evalfail']+=1;return cnt,ex
    cnt['n']+=1
    def X(tag,info=''):
        cnt[tag]+=1
        if tag not in ex or len(M)<ex[tag][0]:ex[tag]=(len(M),ms(M),str(info)[:300])
    par0=lambda i:C.e.par(0,i);par1=lambda i:C.e.par(1,i)
    vOpt=lambda p:C.v(p) if p is not None else Z
    bump=lambda i:(M[i][0]+1,M[i][1],1)
    def nbpar(i):
        p=par0(i)
        if p is None:return True
        g=par0(p);return g is None or M[p]!=bump(g)
    def strong(V,W):return all(not lt(r,W) or lhd(r,W) for r in invd.summ(V))
    k1=C.upg(x-1)
    def upgbad_xm1():
        if k1 is None:return False
        V=vOpt(par1(x-1));return any(not strong(V,W) for W in invd.decomps(V,C.v(k1)))
    UB=upgbad_xm1()
    p1=par0(x-1);g1=par0(p1) if p1 is not None else None
    bpar=g1 is not None and M[p1]==bump(g1)
    badpos=bpar and invd.anc0(C,g1,x)
    def cntx(i):
        cc=[c for c in C.ch(i) if C.counted(i,c)]
        if not cc:return True
        if not all(c==x for c in cc):return False
        return (nbpar(i) and i==x-1 and UB) or (UB and badpos)
    b2=None
    for i in range(x):
        a,b=T.v(i),C.v(i)
        if a==b:continue
        if not isOT(a):X('PV2.FAIL.notOT',i);continue
        if lhdE(a,b):cnt['lhd']+=1;continue
        cnt['weak']+=1
        wk=lt(a,b) and le(ONE,a)
        cs=D.CS(a);pa=vOpt(par0(i));w1=cs or D.WCS(pa,a);w2=cs or WCS2(pa,a);cx=cntx(i)
        if not w1:cnt['weak.WCSPfail']+=1
        if not w1 and w2:cnt['weak.WCSPfail.WCSP2ok']+=1
        if not(wk and w1 and cx):
            if b2 is None:b2=invd.bad2(M)
            X('PV.FAIL.bad2=%s'%b2,i)
        if not(wk and w2 and cx):
            if b2 is None:b2=invd.bad2(M)
            X('PV2.FAIL.bad2=%s.wk=%d.wcs2=%d.cntx=%d.xm1=%d'%(b2,wk,w2,cx,i==x-1),i)
    return cnt,ex
def work(b):
    cnt=collections.Counter();ex={}
    for M in b:
        try:c,e=probe(M)
        except Exception as er:
            c=collections.Counter({'exc.'+type(er).__name__:1});e={'exc':(len(M),ms(M),repr(er)[:200])}
        cnt.update(c)
        for k,v in e.items():
            if k not in ex or v[0]<ex[k][0]:ex[k]=v
    return cnt,ex
def load(f):
    mats=pickle.load(open(f,'rb'))
    if isinstance(mats,dict):mats=mats['seeds']+mats['ext'] if 'seeds' in mats else list(mats.values())
    return [m if not isinstance(m,(bytes,bytearray)) else [tuple(m[i:i+3]) for i in range(0,len(m),3)] for m in mats]
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
