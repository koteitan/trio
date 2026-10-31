"""WfQrO: M[1]-side form of TrigN. At every triggered-arg last-child o frame (i, c < x) of M (q = r, M < SRO):
 V1eq   : v_{M1}(i) = v(i), pre_{M1}(i,L) = pre(i,L), c in M1 child list of i with same L    (M1 = M.take x)
 Trig1  : Trig v pre s y1 at o_{M1}(c) = psi_s(y1)  (trigger already in M[1])
 Sub1   : o_{M1}(c) has subscript s
 Le1N   : y1 <= yN   (n = 2, 3)
 Cut    : y1 = cut(y) (base summand deleted along the DQ path)
also chain monotone: yN(n=2) <= yN(n=3)."""
import sys,os,pickle,json,collections,time,random
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQrO')
from trail import *
def cut(t,tN,eta,k=False):
    """delete the base summand along the DQ path; returns None if fails"""
    if k:
        sy=O.summ(t);sN=O.summ(tN);B=sy[:-1];l=sy[-1]
        if sN[:len(B)]!=B:raise AssertionError
        lN=sN[-1] if len(sN)>len(B) else Z
        cl=cut(l,lN,eta)
        return O.mk(B+([cl] if cl!=Z else []))
    s,y,_=t;s2,y2,_=tN
    if s==s2 and y!=Z and y2!=y:
        try:return (s,cut(y,y2,eta,True),Z)
        except AssertionError:pass
    if y==Z and y2==Z and s!=s2:
        try:return (cut(s,s2,eta,True),Z,Z)
        except AssertionError:pass
    if fsD(t,eta)!=tN:raise AssertionError
    return Z
def check1(M,cnt,ex):
    x=len(M)-1
    if x<1 or M[x][1]==0 or M[x][2]!=0:return
    C=Ctx(M)
    if not C.ok:return
    r=C.e.par(1,x)
    if r is None or C.e.par(0,x)!=r:return
    D=dependencies(C,x);C1=Ctx(M[:x])
    A=C.o(r);mu,br,_=A;seed=C1.o(r);dl=lift_counts(C,x,A)
    def note(f,b,key):
        cnt[f+('.ok' if b else '.FAIL')]+=1
        if not b and (f not in ex or key[0]<ex[f][0]):ex[f]=key
    Ns={n:Ctx([tuple(c) for c in trio.expand([list(c) for c in M],n)]) for n in (2,3)}
    for i in range(x):
        if (True,i) not in D or (False,i) in D:continue
        CLi=C.CL(i)
        if not CLi or (True,CLi[-1]) not in D:continue
        c=CLi[-1];L=C.ch(i)[:C.ch(i).index(c)]
        pre=C.pre(i,L);v=C.v(i);oc=C.o(c)
        s,y,_=oc
        if y==Z or not O.trig(v,pre,s,y):continue
        key=(len(M),ms(M),i,c)
        prev=None
        if c==r:
            note('cr.pre0',pre==Z,key)
            for n in (2,3):
                CN=Ns[n]
                if CN.ok:note('cr.TrigN',O.trig(v,pre,s,CN.o(c)[1]) if CN.o(c)[0]==s else False,key)
            continue
        for n in (2,3):
            CN=Ns[n]
            if not CN.ok:continue
            oN=CN.o(c);s2,y2,_=oN
            if not(s2==s and y2!=y):continue
            cnt['frames.n%d'%n]+=1
            eta=gamS(mu,br,seed,n-2+dl[c])
            if c>=x:note('cx',False,key);continue
            ch1=C1.ch(i);ok1=c in ch1 and ch1[:ch1.index(c)]==L
            note('V1eq',ok1 and C1.v(i)==v and C1.pre(i,L)==pre,key)
            o1=C1.o(c);s1,y1,_=o1
            note('Sub1',s1==s,key)
            t1=O.trig(v,pre,s,y1);note('Trig1',t1,key)
            note('Le1N',le(o1,oN),key)
            note('Le1Ny',s1==s and le(y1,y2),key)
            try:cu=cut(y,y2,eta,True);note('Cut',cu==y1,key);note('PreCut',le(pre,cu),key)
            except AssertionError:note('cutfail',False,key)
            if prev is not None:note('MonoN',le(prev,oN),key)
            prev=oN
def work(batch):
    cnt=collections.Counter();ex={}
    for mm in batch:
        M=[tuple(c) for c in mm]
        try:check1(M,cnt,ex);cnt['mats']+=1
        except Exception as e:
            cnt['exc.'+type(e).__name__]+=1
            if 'exc' not in ex:ex['exc']=(len(M),ms(M),repr(e)[:200])
    return cnt,ex
if __name__=='__main__':
    from multiprocessing import Pool
    out=open(sys.argv[1],'a');npr=int(os.environ.get('NPR','3'))
    for f in sys.argv[2:]:
        t=time.time();mats=pickle.load(open(f,'rb'))
        CAP=int(os.environ.get('CAP','0'))
        if CAP and len(mats)>CAP:random.seed(1);mats=random.sample(list(mats),CAP)
        cnt=collections.Counter();ex={}
        with Pool(npr) as pool:
            for c,e in pool.imap_unordered(work,(mats[i:i+50] for i in range(0,len(mats),50))):
                cnt.update(c)
                for k,v in e.items():
                    if k not in ex or v[0]<ex[k][0]:ex[k]=v
        out.write(json.dumps({'set':os.path.basename(f),'n':len(mats),'sec':round(time.time()-t),'cnt':dict(sorted(cnt.items())),'ex':ex},default=str)+'\n');out.flush()
