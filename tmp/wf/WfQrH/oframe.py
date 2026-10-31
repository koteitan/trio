"""WfQrH: fields of WfQrH2 (frame_step_reduce / trigN_of_pre / frame_step_trigArg) on true values of M[n], n = 2, 3.
Every last-child o frame (i in D true, i not in D false, c = last counted child in D):
 form.{same,sub,arg,base.leaf,base.other}  (DQ constructor at o(c) -> o_N(c), read from the shapes)
 base.leaf: c == x and o(x) = Omega_{a+1} (leaf parent; hBase is the leafpar/add lemma)
 arg & no trigger in M: add (no field needed; check sanity: no trigger in N)
 arg & trigger in M:
   PreB  : pre <= init(y)            (M-side, trigN_of_pre)
   lNz   : last(yN) != 0             (lN != 0)
   TrigN : trigger in N              (sanity: implied by PreB + lNz)
   Last  : lo(y) = 0 -> last(y) = Omega_{s+1} or last(yN) >= Omega_{s+1}
usage: nice -n 15 python3 oframe.py NPROC OUT.jsonl PKL..."""
import sys,os,pickle,json,collections,time
from multiprocessing import Pool
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvA')
import trio
from probe_inv3_prefix import Z, lt, isOT, split, succ, last, isSucc
from probe_adn import dependencies, Ctx, ms, gamS, lift_counts
import ytosk_eval as YE
from probe_inv3_prefix import ONE, sumN
E0=(Z,(ONE,Z,Z),Z)
def summ(t):
    r=[]
    while t:r.append((t[0],t[1],Z));t=t[2]
    return r
def mk(l):
    t=Z
    for s in reversed(l):t=(s[0],s[1],t)
    return t
def le(a,b):return a==b or lt(a,b)
def trig(v,pre,s,y):return lt(pre,y) and lt((v,Z,Z),(s,y,Z))
def check(M,cnt,ex):
    def bad(f,key):
        cnt[f+'.FAIL']+=1
        if f not in ex or key[0]<ex[f][0]:ex[f]=key
    def ok(f,key=None):cnt[f+".ok"]+=1
    x=len(M)-1
    if x<1 or M[x][1]==0 or M[x][2]!=0:return
    C=Ctx(M)
    if not C.ok:return
    r=C.e.par(1,x)
    if r is None or C.e.par(0,x)!=r:return
    D=dependencies(C,x);cnt['frames']+=1
    A=C.o(r);mu,br,_=A;seed=Ctx(M[:x]).o(r);dl=lift_counts(C,x,A)
    for n in (2,3):
        N=[tuple(c) for c in trio.expand([list(c) for c in M],n)];CN=Ctx(N)
        if not CN.ok:cnt['Nevalfail']+=1;continue
        for i in range(x):
            if (False,i) in D and M[i][1] and M[i][2]:
                for j in [j for j in C.ch(i) if M[j]==C.e.bump(i)]:
                    if not C.ch(j):continue
                    G=sumN([C.o(e) for e in C.ch(j)]);GN=sumN([CN.o(e) for e in C.ch(j)])
                    S=sumN([ONE]+[C.bumpTerm(i,jj) for jj in C.ch(i)]);SN=sumN([ONE]+[CN.bumpTerm(i,jj) for jj in C.ch(i)])
                    for lay,(Y_,YN_) in (('1',(G,GN)),('2',(S,SN))):
                        if Y_==YN_:cnt['lay.same']+=1;continue
                        sm=lt(Y_,E0);smN=lt(YN_,E0)
                        if sm and smN:cnt['lay.small']+=1
                        elif not sm and not smN and Y_[2]!=Z:cnt['lay.multi']+=1
                        elif not sm and not smN:cnt['lay.single']+=1
                        elif Y_==E0:cnt['lay.crossE0']+=1
                        else:bad('lay.crossOther',(len(M),ms(M),n,i))
            if (True,i) not in D or (False,i) in D:continue
            CLi=C.CL(i)
            if not CLi or (True,CLi[-1]) not in D:continue
            c=CLi[-1];L=C.ch(i)[:C.ch(i).index(c)]
            pre=C.pre(i,L);v=C.v(i);oc=C.o(c);oN=CN.o(c)
            key=(len(M),ms(M),n,i,c)
            s,y,_=oc;s2,y2,_=oN
            if oN==oc:cnt['form.same']+=1;continue
            if y==Z and s2!=s and y2==Z and not (c==x):cnt['form.sub']+=1;continue
            if y==Z and isSucc(s) if s else False:
                cnt['form.base.leaf'+('.x' if c==x else '.notx')]+=1
                if c!=x:bad('form.base.leaf.notx',key);continue
                (ok if lt(oN,oc) and oN!=Z and not oN[2] else bad)('Leaf.lt',key)
                if not trig(v,pre,s2,y2):ok('Leaf.add');continue
                th=(succ(s2),Z,Z);hi,lo=split(y2,th)
                ad=summ(YE.add(pre,oc));Bl=ad[:-1];hil=summ(hi)
                okL=lo!=Z and ad[-1]==oc and hil[:len(Bl)]==Bl and all(not lt(q,oN) and lt(q,oc) for q in hil[len(Bl):])
                (ok if okL else bad)('Leaf.leafpar',key)
                continue
            if s2==s and y2!=y and y!=Z:
                sy=summ(y);sN=summ(y2)
                if not(len(sN)>=len(sy) and sN[:len(sy)-1]==sy[:-1]):cnt['form.other']+=1;bad('form.other',key);continue
                cnt['form.arg']+=1
                tM=trig(v,pre,s,y);tN=trig(v,pre,s,y2)
                if not tM:
                    (ok if not tN else bad)('arg.noTrigM.noTrigN',key);continue
                B=mk(sy[:-1]);l=sy[-1];lN=sN[-1]
                (ok if le(pre,B) else bad)('PreB',key)
                (ok if lt(pre,mk(sy[:-1]+[(l[0],Z,Z)])) else bad)('PreS',key)
                (ok if (lN[0]==l[0] or le(pre,B)) else bad)('lNsub',key)
                (ok if lN!=Z else bad)('lNz',key)
                (ok if l!=ONE else bad)('lastNotOne',key)
                eta=gamS(mu,br,seed,n-2+dl[c])
                (ok if lt(pre,seed) else bad)('PreSeed',key)
                (ok if lt(pre,eta) else bad)('PreEta',key)
                (ok if le(eta,lN) else bad)('lNgeEta',key)
                (ok if (le(pre,B) or lt(pre,eta)) else bad)('PreBorEta',key)
                (ok if tN else bad)('TrigN',key)
                th=(succ(s),Z,Z)
                if split(y,th)[1]==Z:
                    (ok if (l==th or not lt(lN,th)) else bad)('Last',key)
                continue
            cnt['form.base.other'+('.x' if c==x else '.notx')]+=1
            if c!=x:bad('form.base.other.notx',key)
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
    npr=int(sys.argv[1]);out=open(sys.argv[2],'a')
    for f in sys.argv[3:]:
        t=time.time();mats=pickle.load(open(f,'rb'))
        CAP=int(os.environ.get('CAP','0'))
        if CAP and len(mats)>CAP:
            import random;random.seed(1);mats=random.sample(list(mats),CAP)
        cnt=collections.Counter();ex={}
        with Pool(npr) as pool:
            for c,e in pool.imap_unordered(work,(mats[i:i+50] for i in range(0,len(mats),50))):
                cnt.update(c)
                for k,v in e.items():
                    if k not in ex or v[0]<ex[k][0]:ex[k]=v
        out.write(json.dumps({'set':os.path.basename(f),'n':len(mats),'sec':round(time.time()-t),'cnt':dict(sorted(cnt.items())),'ex':ex},default=str)+'\n');out.flush()
