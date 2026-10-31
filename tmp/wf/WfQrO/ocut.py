"""WfQrO: cut fields of the triggered-argument o frame (Lean WfQrO1).  Every last-child o frame (i in D true, not
D false, c = last counted child in D, c < x), arg form o(c) = psi_s(y) -> o_N(c) = psi_s(yN), trigger in M, n = 2, 3.
 cut(y)    : DQcut (structural sub/arg first, base l -> fsD(l, eta) with fsD != 0; deleted to 0)
 CutEx     : a DQcut derivation exists (with lN = last summand decompositions)
 PreCut    : pre <= cut(y)                       (-> TrigN, WfQrO1.trigN_of_cut)
 PreB      : pre <= init(y)  (old, false)
 LastNot1  : last(y) != 1 ; EtaNz: eta != 0     (-> lNz)
 LastCut   : lo(y) = 0 -> l = Om_{s+1} or Om_{s+1} <= cut(l)    (-> Last)
 LastAlt   : some other decomposition yN = B ++ Q' ++ lN' with lN' = fsD(l, eta) multi-summand (would need l = Om_{s+1})
 M1 side   : CR.pre0 (c = r -> pre = 0); Trig1orB (trigger in M.take x or pre <= init y); Y1leCut (y1 <= cut(y))
usage: CAP=2000 NPR=3 nice -n 15 python3 ocut.py OUT.jsonl PKL..."""
import sys,os,pickle,json,collections,time,random
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQrO')
from trail import *
def cutT(t,tN,eta,k=False):
    if k:
        sy=O.summ(t);sN=O.summ(tN);B=sy[:-1];l=sy[-1]
        if len(sN)<=len(B) or sN[:len(B)]!=B:raise AssertionError('mk')
        lN=sN[-1]
        if not all(le(lN,q) and lt(q,l) for q in sN[len(B):-1]):raise AssertionError('Q')
        cl=cutT(l,lN,eta)
        return O.mk(B+([cl] if cl!=Z else []))
    if t==Z or tN==Z:raise AssertionError('z')
    s,y,_=t;s2,y2,_=tN
    if tN[2]==Z:
        if s==s2 and y!=Z and y2!=y:
            try:return (s,cutT(y,y2,eta,True),Z)
            except AssertionError:pass
        if y==Z and y2==Z and s!=s2:
            try:return (cutT(s,s2,eta,True),Z,Z)
            except AssertionError:pass
    if fsD(t,eta)!=tN or not lt(tN,t):raise AssertionError('base')
    return Z
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
        if y==Z or not O.trig(v,pre,s,y):continue
        for n in (2,3):
            if n not in Ns:Ns[n]=Ctx([tuple(cc) for cc in trio.expand([list(cc) for cc in M],n)])
            CN=Ns[n]
            if not CN.ok:continue
            oN=CN.o(c);s2,y2,_=oN
            if not(s2==s and y2!=y):continue
            key=(len(M),ms(M),n,i,c)
            cnt['frames']+=1
            eta=gamS(mu,br,seed,n-2+dl[c])
            sy=O.summ(y);sN=O.summ(y2);B=O.mk(sy[:-1]);l=sy[-1];lN=sN[-1]
            note('EtaNz',eta!=Z,key);note('LastNot1',l!=ONE1,key)
            note('PreB.old',le(pre,B),key)
            try:yc=cutT(y,y2,eta,True)
            except AssertionError as e:note('CutEx',False,key);cnt['CutEx.why.'+str(e)]+=1;continue
            note('CutEx',True,key);note('CutLt',lt(yc,y2),key)
            note('PreCut',le(pre,yc),key)
            if c==r:note('CR.pre0',pre==Z,key)
            else:
                o1=C1.o(c)
                t1=o1[0]==s and O.trig(v,pre,s,o1[1])
                note('Trig1orB',t1 or le(pre,B),key)
                if o1[0]==s:note('Y1leCut',le(o1[1],yc),key)
            th=(succ(s),Z,Z)
            if split(y,th)[1]==Z:
                lc=cutT(l,lN,eta)
                note('LastCut',l==th or le(th,lc),key)
                f=fsD(l,eta);sf=O.summ(f)
                alt=len(sf)>1 and sN[len(sN)-len(sf):]==sf and len(sN)-len(sf)>=len(sy)-1
                if alt:note('LastAlt',l==th or all(not lt(q,th) for q in sf),key)
def work(batch):
    cnt=collections.Counter();ex={}
    for mm in batch:
        M=[tuple(c) for c in mm]
        try:check(M,cnt,ex);cnt['mats']+=1
        except Exception as e:
            cnt['exc.'+type(e).__name__]+=1
            if 'exc' not in ex:ex['exc']=(len(M),ms(M),repr(e)[:200])
    return cnt,ex
ONE1=(Z,Z,Z)
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
