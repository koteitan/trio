"""WfSdH: BumpAbsCB with WCSP2 (2026-11-01).
BumpAbsCB2 at i (exact Lean guard of BumpAbsCB, as in WfInvD/invd.py 'ab'):
  strong absorption (every summand r of v(P1 i) with not r < W', r < W is lhd W)  or
  (WkVA v'(i) v(i) and (CS v'(i) or WCS2 v(P0 i) v'(i)) and CntX i).
Counts: guarded cases, absorption failures, old weak branch (WCSP) holds, new (WCSP2) holds; failures of each.
usage: nice -n 15 python3 abcb2.py NPROC PKL..."""
import sys,os,pickle,json,collections,time
from multiprocessing import Pool
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.append('/home/koteitan/proofs/trio/tmp/codex')
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvD');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfDrE')
from probe_inv3_prefix import Ctx,Z,ONE,lt,le,isOT
from lhd_exact import lhd,lhdE,comps
import probe_dropres as D
import ytosk_eval as Y
import invd,pv2
SRO=invd.SRO;ms=invd.ms;summ=invd.summ
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
    def strong(V,W):return all(not lt(r,W) or lhd(r,W) for r in summ(V))
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
    def wkva(a,b):return lt(a,b) and le(ONE,a) and isOT(a)
    t=2 if M[x][2] else (1 if M[x][1] else 0)
    p0x=par0(x);q=p0x;xparnb=True
    if q is not None:
        g=par0(q)
        if g is not None and M[q]==bump(g):xparnb=False
    vx0=(C.v(x)==Z)
    b2=None
    for i in range(n):
        if not C.e12(i):continue
        bj=[j for j in C.ch(i) if M[j]==bump(i)]
        if not all(C.ch(j)!=[x] or vx0 for j in bj):continue
        sg=True
        for jl in (T.ch(i) if i<x else []):
            if M[jl]!=bump(i):continue
            if not D.BRelS(D.sumN([T.o(k) for k in T.ch(jl)]),D.sumN([C.o(k) for k in C.ch(jl)])):sg=False;break
        if not(sg or xparnb or vx0):continue
        cnt['guard']+=1
        W=C.bumpW(i);W1=T.bumpW(i) if i<x else Y.omega(ONE)
        if all(lt(r,W1) or not lt(r,W) or lhd(r,W) for r in summ(vOpt(par1(i)))):continue
        cnt['absfail']+=1
        if i>=x:
            if b2 is None:b2=invd.bad2(M)
            X('FAIL.i=x.t%d.bad2=%s'%(t,b2),i);continue
        a,b=T.v(i),C.v(i);pa=vOpt(par0(i));cs=D.CS(a)
        wk=wkva(a,b);cx=cntx(i);w1=cs or D.WCS(pa,a);w2=cs or pv2.WCS2(pa,a)
        if wk and w1 and cx:cnt['CB.ok']+=1
        if wk and w2 and cx:cnt['CB2.ok']+=1
        if not(wk and w1 and cx):
            if b2 is None:b2=invd.bad2(M)
            X('CB.FAIL.t%d.bad2=%s.wk=%d.wcs=%d.cntx=%d'%(t,b2,wk,w1,cx),i)
        if not(wk and w2 and cx):
            if b2 is None:b2=invd.bad2(M)
            X('CB2.FAIL.t%d.bad2=%s.wk=%d.wcs2=%d.cntx=%d'%(t,b2,wk,w2,cx),i)
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
if __name__=='__main__':
    npr=int(sys.argv[1]);lim=int(os.environ.get('LIMIT','0'))
    for f in sys.argv[2:]:
        t0=time.time();mats=pv2.load(f)
        if lim and len(mats)>lim:
            import random;random.seed(5);mats=random.sample(mats,lim)
        cnt=collections.Counter();ex={}
        with Pool(npr) as p:
            for c,e in p.imap_unordered(work,(mats[i:i+50] for i in range(0,len(mats),50))):
                cnt.update(c)
                for k,v in e.items():
                    if k not in ex or v[0]<ex[k][0]:ex[k]=v
        print(json.dumps({'set':f.split('/')[-1],'n':len(mats),'sec':round(time.time()-t0),'cnt':dict(sorted(cnt.items())),'ex':ex}),flush=True)
