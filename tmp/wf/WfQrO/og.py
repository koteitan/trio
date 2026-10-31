"""WfQrO: the fields OG of WfQrO1 (exact search for DQG witnesses), at every triggered-argument last-child o frame
(c < x; q = r; M < SRO), n = 2, 3.
 sumG(p, t, tN) : exists tc (rules mk, mkQ, base, sub, arg, low) with DQG eta true t tN tc and p <= tc;  oneG(p, l, lN) : same with false.
 PreG     : sumG(pre, y, yN)                                      -> TrigN (trigN_of_G)
 LastNot1 : last(y) != 1 ;  EtaNz : eta != 0                      -> lNz (lNz_of)
 LastG    : every decomposition yN = B ++ Q ++ lN with DQ eta false l lN, lo(y) = 0:
            l = Om_{s+1} or (lN single and oneG(Om_{s+1}, l, lN))  -> Last (last_of_G)
 PreB.old : pre <= init(y) (false; for comparison); CR.pre0 : c = r -> pre = 0
usage: CAP=2000 NPR=3 nice -n 15 python3 og.py OUT.jsonl PKL..."""
import sys,os,pickle,json,collections,time,random
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQrO')
from trail import *
ONE1=(Z,Z,Z)
class G:
    def __init__(s,eta):s.eta=eta;s.memo={}
    def splits(s,t,tN):
        """t = B ++ l; yields (l, lN) for tN = B ++ Q ++ lN with lN <= q < l for q in Q (lN nonempty)."""
        if t==Z:return
        sy=O.summ(t);sN=O.summ(tN);B=sy[:-1];l=sy[-1]
        if len(sN)<=len(B) or sN[:len(B)]!=B:return
        for j in range(len(B),len(sN)):
            lN=O.mk(sN[j:]);Q=sN[len(B):j]
            if all(le(lN,q) and lt(q,l) for q in Q):yield O.mk(B),l,lN,O.mk(B+Q)
    def sumG(s,p,t,tN,dq=False):
        k=('s',p,t,tN,dq)
        if k in s.memo:return s.memo[k]
        res=False
        for B0,l,lN,BQ in s.splits(t,tN):
            for B in ((B0,BQ) if BQ!=B0 else (B0,)):   # mk / mkQ
                if le(p,B):ok=s.oneG(Z,l,lN,dq)
                else:
                    sp=O.summ(p);sB=O.summ(B)
                    ok=len(sp)>len(sB) and sp[:len(sB)]==sB and s.oneG(O.mk(sp[len(sB):]),l,lN,dq)
                if ok:break
            if ok:res=True;break
        s.memo[k]=res;return res
    def oneG(s,p,l,lN,dq=False):
        """p: a sum (the rest of the comparison); l single; dq=True: plain DQ existence (p = 0, base without != 0)."""
        k=('o',p,l,lN,dq)
        if k in s.memo:return s.memo[k]
        res=False;eta=s.eta
        f=fsD(l,eta)
        if f==lN and lt(f,l) and (lt(p,lN) or (dq and p==Z)):res=True
        if not res and lN!=Z and lN[2]==Z:
            a,b,_=l;aN,bN,_=lN
            if b==Z and bN==Z:
                pa=p[0] if p else Z
                if s.sumG(pa,a,aN,dq):res=True
            elif a==aN:
                if p==Z or lt(p[0],a):res=s.sumG(Z,b,bN,dq)
                elif p[0]==a:res=s.sumG(p[1],b,bN,dq)
        s.memo[k]=res;return res
def check(M,cnt,ex):
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
    Ns={}
    for i in range(x):
        if (True,i) not in D or (False,i) in D:continue
        CLi=C.CL(i)
        if not CLi or (True,CLi[-1]) not in D:continue
        c=CLi[-1]
        if c>=x:continue
        L=C.ch(i)[:C.ch(i).index(c)]
        pre=C.pre(i,L);v=C.v(i);oc=C.o(c)
        s,y,_=oc
        if y==Z:continue
        tM=O.trig(v,pre,s,y)
        for n in (2,3):
            if n not in Ns:Ns[n]=Ctx([tuple(cc) for cc in trio.expand([list(cc) for cc in M],n)])
            CN=Ns[n]
            if not CN.ok:continue
            oN=CN.o(c);s2,y2,_=oN
            if not(s2==s and y2!=y):continue
            key=(len(M),ms(M),n,i,c)
            eta=gamS(mu,br,seed,n-2+dl[c]);g=G(eta)
            note('DQ',g.sumG(Z,y,y2,True),key)
            if not tM:continue
            cnt['frames']+=1
            sy=O.summ(y);B=O.mk(sy[:-1]);l=sy[-1]
            note('EtaNz',eta!=Z,key);note('LastNot1',l!=ONE1,key)
            note('PreB.old',le(pre,B),key)
            note('PreG',g.sumG(pre,y,y2),key)
            if c==r:note('CR.pre0',pre==Z,key)
            th=(succ(s),Z,Z)
            if split(y,th)[1]==Z:
                for B_,l_,lN,_ in g.splits(y,y2):
                    if not g.oneG(Z,l_,lN,True):continue
                    note('LastG',l_==th or (lN[2]==Z and g.oneG(th,l_,lN)),key)
def work(batch):
    cnt=collections.Counter();ex={}
    for mm in batch:
        M=[tuple(c) for c in mm]
        try:check(M,cnt,ex);cnt['mats']+=1
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
