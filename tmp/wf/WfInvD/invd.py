"""WfInvD probe (2026-10-31): HDropU repair candidates.
For each M (x = |M|-1, sigma = Ctx(M), sigma' = Ctx(M[:-1])):
 ua cases at i = x-1 (exact Lean DropResHB.ua):  per decomposition v(k) = V + W (W != 0):
   strong / wcsp (Lean WCSP) / cmp (comps z (V+1) < psi(V+1)) / nbx (NBParX) ;  classified by t, P0 x = x-1, k = P0(x-1).
 ab: BumpAbsC failures (exact Lean guard), and at each failing i the weak alternative of BumpAbsCB
   (WkVA v'(i) v(i), WCSP i v'(i), CntX i), and whether PV holds at i (drop conclusion, exact Lean PV).
 bad2 (codex exact) and the new class B2X = P0 x = x-1, e1 x != 0, BumpAbsC fails (no upgrade / bump-parent conjunct).
usage: nice -n 15 python3 invd.py NPROC PKL...
"""
import sys,os,pickle,json,collections,time
from multiprocessing import Pool
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.append('/home/koteitan/proofs/trio/tmp/codex')
from probe_inv3_prefix import Ctx,Z,ONE,lt,le,isOT
from lhd_exact import lhd,lhdE,comps
import probe_dropres as D
import ytosk_eval as Y
SRO=[(0,0,0),(1,1,1),(2,1,1),(3,1,0),(2,0,0)]
def ms(M):return ''.join('(%d,%d,%d)'%tuple(c) for c in M)
def summ(t):
    out=[]
    while t:out.append((t[0],t[1],Z));t=t[2]
    return out
def decomps(V,vk):
    W=vk
    while W:
        if Y.add(V,W)==vk:yield W
        W=W[2]
def anc0(C,a,d):
    while d is not None:
        if d==a:return True
        if d<a:return False
        d=C.e.par(0,d)
    return False
_bad2=None
def bad2(M):
    global _bad2
    if _bad2 is None:
        import bad2_exact_trio_codex as B;from huac_structure_trio_codex import Ctx as HC;_bad2=(B,HC)
    B,HC=_bad2
    return B.bad2(HC(M),HC(M[:-1]))[0]
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
    def wcsp(i,w):return D.CS(w) or D.WCS(vOpt(par0(i)),w)
    def wkva(a,b):return lt(a,b) and le(ONE,a) and isOT(a)
    def strong(V,W):return all(not lt(r,W) or lhd(r,W) for r in summ(V))
    k1=C.upg(x-1)
    def upgbad_xm1():
        if k1 is None:return False
        V=vOpt(par1(x-1));return any(not strong(V,W) for W in decomps(V,C.v(k1)))
    UB=upgbad_xm1()
    p1=par0(x-1);g1=par0(p1) if p1 is not None else None
    bpar=g1 is not None and M[p1]==bump(g1)
    badpos=bpar and anc0(C,g1,x)
    def cntx(i):
        cc=[c for c in C.ch(i) if C.counted(i,c)]
        if not cc:return True
        if not all(c==x for c in cc):return False
        return (nbpar(i) and i==x-1 and UB) or (UB and badpos)
    def pv(i):
        a,b=T.v(i),C.v(i)
        if not isOT(a):return False
        return a==b or lhdE(a,b) or (wkva(a,b) and wcsp(i,a) and cntx(i))
    t=2 if M[x][2] else (1 if M[x][1] else 0)
    p0x=par0(x);xm1=(p0x==x-1)
    q=p0x;xparnb=True
    if q is not None:
        g=par0(q)
        if g is not None and M[q]==bump(g):xparnb=False
    vx0=C.v(x)==Z
    # ---- ua
    if k1 is not None:
        i=x-1;V=vOpt(par1(i));w=Y.add(V,ONE)
        wc=wcsp(i,w);cm=all(lt(g,(w,Z,Z)) for g in comps(Z,w))
        for W in decomps(V,C.v(k1)):
            cnt['ua.cases']+=1
            if strong(V,W):cnt['ua.strong']+=1;continue
            key='t%d.xm1=%d.kP0=%d'%(t,xm1,k1==p1)
            if wc and cm:cnt['ua.side.'+key]+=1;continue
            if not wc:X('ua.FAIL.noWCSP.'+key,(i,k1,Y.tstr(W)))
            else:X('ua.FAIL.cmpOnly.'+key,(i,k1,Y.tstr(W),'pv(x-1)=%s'%pv(i)))
    # ---- ab (BumpAbsC, exact guard)
    abfail=[]
    for i in range(n):
        if not C.e12(i):continue
        bj=[j for j in C.ch(i) if M[j]==bump(i)]
        if not all(C.ch(j)!=[x] or vx0 for j in bj):continue
        sg=True
        for jl in (T.ch(i) if i<x else []):
            if M[jl]!=bump(i):continue
            if not D.BRelS(D.sumN([T.o(k) for k in T.ch(jl)]),D.sumN([C.o(k) for k in C.ch(jl)])):sg=False;break
        if not(sg or xparnb or vx0):continue
        W=C.bumpW(i);W1=T.bumpW(i) if i<x else Y.omega(ONE)
        for r in summ(vOpt(par1(i))):
            if not lt(r,W1) and lt(r,W) and not lhd(r,W):abfail.append(i);break
    b2=None
    if abfail:
        b2=bad2(M)
        shape2=xm1 and M[x][1]!=0
        def bas(i):
            m=par0(i)
            if m is None or par1(i)!=m or i>=x:return False
            if C.CL(i) or T.CL(i):return False
            cm=C.CL(m);ct=T.CL(m)
            if not cm or cm[-1]!=i or cm!=ct:return False
            if any(T.o(d)!=C.o(d) for d in cm[:-1]) or T.v(m)!=C.v(m):return False
            return all(C.upg(j)!=i for j in range(n))
        for i in abfail:
            if (t==0 or (t==2 and not b2)) and not bas(i):X('HDropUg.ab.FAIL.t%d'%t,i)
            cnt['ab.bas=%d.t%d.bad2=%s'%(bas(i),t,b2)]+=1
        for i in abfail:
            weak=i<x and wkva(T.v(i),C.v(i)) and wcsp(i,T.v(i)) and cntx(i)
            key='ab.FAIL.t%d.bad2=%s.shape2=%d.CB=%d.PV=%s'%(t,b2,shape2,weak,pv(i) if i<x else '-')
            X(key,(i,'k1=%s bpar=%s'%(k1,bpar)))
        if not b2 and not (t!=0 and M[x][1]==0):
            X('HDropU.ab.FAIL.t%d.shape2=%d.upg=%d.bpar=%d'%(t,shape2,k1 is not None,bpar))
        if shape2 and not b2:X('B2X.new.t%d.upg=%d.bpar=%d'%(t,k1 is not None,bpar))
    # t = 1, q = r: the seed condition of qr_dropSeed (Lean qr_seedC_of conclusion), outside Bad2
    if t==1 and p0x is not None and par1(x)==p0x:
        r_=p0x;o1=T.o(r_);o=C.o(r_)
        ok=lhd(o1,o) or (o1 and o1[1]==Z and o1[2]==Z and lt(o1[0],C.v(r_)) and all(lt(g,(o1[0],Z,Z)) for g in comps(Z,o1[0])))
        cnt['qrSeedC.cases']+=1
        if not ok:
            bb=bad2(M) if b2 is None else b2
            X('qrSeedC.FAIL.bad2=%s.L1=%d'%(bb,r_==x-1),(r_,Y.tstr(o1)[:80]))
    # PV everywhere (drop conclusion) - only report failures
    for i in range(x):
        if not pv(i):X('PV.FAIL.bad2=%s'%(bad2(M) if b2 is None else b2),i);break
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
    npr=int(sys.argv[1])
    for f in sys.argv[2:]:
        t0=time.time();mats=pickle.load(open(f,'rb'))
        if isinstance(mats,dict):mats=mats['seeds']+mats['ext'] if 'seeds' in mats else list(mats.values())
        mats=[m if not isinstance(m,(bytes,bytearray)) else [tuple(m[i:i+3]) for i in range(0,len(m),3)] for m in mats]
        cnt=collections.Counter();ex={}
        with Pool(npr) as p:
            for c,e in p.imap_unordered(work,(mats[i:i+50] for i in range(0,len(mats),50))):
                cnt.update(c)
                for k,v in e.items():
                    if k not in ex or v[0]<ex[k][0]:ex[k]=v
        print(json.dumps({'set':f.split('/')[-1],'n':len(mats),'sec':round(time.time()-t0),'cnt':dict(sorted(cnt.items())),
                          'ex':{k:v for k,v in ex.items() if 'FAIL' in k or 'exc' in k or 'B2X' in k}}),flush=True)
