"""WfQrL step (4): standard form of DQ values inside psi.
For q=r frames: true values of N = M[n] (n = 2..NMAX) on D columns; DQ decomposition with the psi levels on the path.
At every argument level psi_a(b) -> psi_a(bN) on the path ABOVE a non-empty Q, the new components
comps(a, bN) \ comps(a, strip(bN)) (strip = remove every Q) are tested:
  C_ot   : g < bN                       (= isOT; sanity)
  C_strip: g < strip(bN)                 (M-side form: below the old engine value)
  C_lN   : g < lN at the Q level         (below the new last summand of the Q level)
  C_Qq   : for q in Q, every g in comps(a, q) is < q   (component below its own summand)
usage: nice -n 15 python3 compq.py NPROC NMAX OUT.jsonl PKL..."""
import sys,os,pickle,json,collections,time
from multiprocessing import Pool
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvA');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQrE')
import trio
from probe_inv3_prefix import Z, fs, fsD, summ, lt, cof, isSucc, le, comps, isOT
from probe_adn import gamS, dependencies, lift_counts, Ctx, ms
NMAX=3
def mk(l):
    t=Z
    for s in reversed(l):t=(s[0],s[1],t)
    return t
# dq returning (stripped tN, events) or None; events: ('Q',depth,Q,lN) and ('arg',depth,a,bN,bNstrip)
def dq(t,tN,eta,depth=0):
    if not t:return (Z,[]) if not tN else None
    s=summ(t);sN=summ(tN)
    if len(sN)<len(s) or sN[:len(s)-1]!=s[:-1]:return None
    Q=sN[len(s)-1:-1];l=s[-1];lN=sN[-1]
    if any(not(le(lN,q) and lt(q,l)) for q in Q):return None
    r=dq1(l,lN,eta,depth+1)
    if r is None:return None
    lS,ev=r
    return (mk(s[:-1]+[lS]),([('Q',depth,Q,lN)] if Q else [])+ev)
def dq1(t,tN,eta,depth):
    a,b,_=t
    if not b:
        if not a:return (t,[]) if tN==t else None
        if isSucc(a):return (tN,[]) if tN==eta else None
        if tN[1]!=Z or tN[2]!=Z:return None
        r=dq(a,tN[0],eta,depth)
        if r is None:return None
        return ((r[0],Z,Z),r[1])
    if isSucc(b):return (tN,[]) if tN==fsD(t,eta) else None
    if cof(b)[0]=='big':return (tN,[]) if tN==(a,fs(b,eta),Z) else None
    if tN[0]!=a or tN[2]!=Z:return None
    r=dq(b,tN[1],eta,depth)
    if r is None:return None
    bS,ev=r
    return ((a,bS,Z),[('arg',depth,a,tN[1],bS)]+ev)
def test(ev,cnt,ex,key):
    Qs=[e for e in ev if e[0]=='Q']
    if not Qs:return
    for e in ev:
        if e[0]!='arg':continue
        _,d,a,bN,bS=e
        if not any(q[1]>=d for q in Qs):continue
        old=set(comps(a,bS))
        new=[g for g in comps(a,bN) if g not in old]
        cnt['levels']+=1
        if not new:cnt['nonew']+=1;continue
        cnt['withnew']+=1
        for name,ok in (('C_ot',all(lt(g,bN) for g in new)),('C_strip',all(lt(g,bS) for g in new)),
                        ('C_lN',all(any(lt(g,q[3]) for q in Qs if q[1]>=d) for g in new))):
            cnt[name+('.ok' if ok else '.FAIL')]+=1
            if not ok and name not in ex:ex[name]=key
    for q in Qs:
        for e in ev:
            if e[0]=='arg' and e[1]<=q[1]:
                ok=all(all(lt(g,qq) for g in comps(e[2],qq)) for qq in summ(q[2]) if True) if False else all(all(lt(g,qq) for g in comps(e[2],qq)) for qq in q[2])
                cnt['C_Qq'+('.ok' if ok else '.FAIL')]+=1
                if not ok and 'C_Qq' not in ex:ex['C_Qq']=key
def check(M,cnt,ex):
    C=Ctx(M)
    if not C.ok:return
    x=len(M)-1;r=C.e.par(1,x)
    if r is None or C.e.par(0,x)!=r or M[x][2]!=0:return
    T=Ctx(M[:x]);A=C.o(r);mu,br,_=A;seed=T.o(r);D=dependencies(C,x);d=lift_counts(C,x,A)
    for n in range(2,NMAX+1):
        N=[tuple(c) for c in trio.expand([list(c) for c in M],n)];CN=Ctx(N)
        if not CN.ok:cnt['Nevalfail']+=1;continue
        for i in range(x):
            for tag in (True,False):
                if (tag,i) not in D:continue
                t=C.o(i) if tag else C.v(i);tN=CN.o(i) if tag else CN.v(i)
                if tN==t:continue
                eta=gamS(mu,br,seed,n-2+d[i])
                res=dq(t,tN,eta)
                if res is None:cnt['DQFAIL']+=1;ex.setdefault('DQFAIL',(len(M),ms(M),n,tag,i));continue
                if not isOT(tN):cnt['trueNotOT']+=1
                if any(e[0]=='Q' for e in res[1]):cnt['nonfsD']+=1
                test(res[1],cnt,ex,(len(M),ms(M),n,tag,i))
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
        cnt=collections.Counter();ex={}
        with Pool(npr,initializer=globals().__setitem__,initargs=('NMAX',NMAX)) as pool:
            for c,e in pool.imap_unordered(work,(mats[i:i+100] for i in range(0,len(mats),100))):
                cnt.update(c)
                for k,v in e.items():
                    if k not in ex or v[0]<ex[k][0]:ex[k]=v
        out.write(json.dumps({'set':os.path.basename(f),'n':len(mats),'sec':round(time.time()-t),'cnt':dict(sorted(cnt.items())),'ex':ex},default=str)+'\n');out.flush()
