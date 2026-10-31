"""Batch DQ check (WfQrE): for q=r frames, expand M[2], M[3] and compare D values with DQ.
Frames checked: every frame where some absorption (bump AbsW, upgrade AbsU) or TPLo test fails at m = 0..2,
plus every SAMPLE-th frame.  usage: nice -n 15 python3 runq.py NPROC SAMPLE OUT.jsonl FRAMEPKL..."""
import sys,os,pickle,json,collections,time
from multiprocessing import Pool
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvA');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQrE')
from probe_adn import gamS, dependencies, lift_counts, Ctx, Z, fsD, summ, lt, ohole, cof, last, split, succ, isSucc, ms
from cmpq import check
SAMPLE=1
def suspicious(M):
    C=Ctx(M)
    if not C.ok:return False
    x=len(M)-1;r=C.e.par(1,x);T=Ctx(M[:x]);A=C.o(r);mu,br,_=A;seed=T.o(r);D=dependencies(C,x);d=lift_counts(C,x,A)
    for i in range(x):
        if (False,i) in D and M[i][1]:
            Ws=[]
            if C.e12(i):Ws.append(C.bumpW(i))
            elif C.upg(i) is not None:Ws.append(last(C.v(C.upg(i))))
            for W in Ws:
                if not(ohole(W) and cof(W)[0]=='omega'):continue
                for q in summ(C.vOpt1(i)):
                    if lt(q,W) and any(not lt(q,fsD(W,gamS(mu,br,seed,m+d[i]))) for m in range(3)):return True
        if (True,i) in D:
            s,y,_=C.o(i)
            if y==br or not y or split(y,(succ(s),Z,Z))[1]!=Z:continue
            l=last(y)
            if not l or l[1]!=Z:continue
            a=l[0]
            if isSucc(a) or not ohole(a) or cof(a)[0]!='omega':continue
            if any(lt((fsD(a,gamS(mu,br,seed,m+d[i])),Z,Z),(succ(s),Z,Z)) for m in range(3)):return True
    return False
def work(args):
    batch,start=args
    cnt=collections.Counter();ex={}
    for j,mm in enumerate(batch):
        M=[tuple(c) for c in mm]
        try:
            sus=suspicious(M)
            if not sus and (start+j)%SAMPLE:continue
            cnt['checked.sus%d'%int(sus)]+=1
            c,e=check(M,3)
            cnt.update(c)
            for k in c:
                if (k.startswith('FAIL') or k.startswith('DQ.') or k=='sandwich0') and (k not in ex or len(M)<ex[k][0]):ex[k]=(len(M),ms(M),str(e[:3]))
        except Exception as e:
            cnt['exc.'+type(e).__name__]+=1
            if 'exc' not in ex:ex['exc']=(len(M),ms(M),repr(e)[:300])
    return cnt,ex
if __name__=='__main__':
    npr=int(sys.argv[1]);SAMPLE=int(sys.argv[2]);out=open(sys.argv[3],'a')
    for f in sys.argv[4:]:
        t=time.time();mats=pickle.load(open(f,'rb'))
        cnt=collections.Counter();ex={}
        with Pool(npr,initializer=globals().__setitem__,initargs=('SAMPLE',SAMPLE)) as pool:
            for c,e in pool.imap_unordered(work,((mats[i:i+200],i) for i in range(0,len(mats),200))):
                cnt.update(c)
                for k,v in e.items():
                    if k not in ex or v[0]<ex[k][0]:ex[k]=v
        out.write(json.dumps({'set':os.path.basename(f),'n':len(mats),'sec':round(time.time()-t),'cnt':dict(sorted(cnt.items())),'ex':ex})+'\n');out.flush()
