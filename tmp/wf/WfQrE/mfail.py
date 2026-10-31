"""For q=r frames: at which level m does the absorption / TPLoW at chain index k = m + d fail? (WfQrE)
usage: nice -n 15 python3 mfail.py NPROC OUT.jsonl FRAMEPKL...
AbsW(m): D v-call i, e12, OHole W, cof W omega; q in summands vOpt(P1 i), q < W -> q < fsD(W, gamS(m + d_i))
TPLo(m): D o-call c, o(c)=psi_s(y), y != b_r, split(y,Om_{s+1}).2 = 0, last y = psi_a(0)... a not succ, OHole a, cof omega:
         not psi(fsD(a, gamS(m+d_c))) < Om_{s+1}
records histogram of max failing m (m = 0..5) and examples."""
import sys,os,pickle,json,collections,time
from multiprocessing import Pool
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvA')
from probe_adn import gamS, dependencies, lift_counts, Ctx, Z, fsD, summ, lt, ohole, cof, last, split, succ, isSucc, ms, SRO
MM=6
def meas(M,cnt,ex):
    C=Ctx(M)
    if not C.ok:cnt['evalfail']+=1;return
    x=len(M)-1;r=C.e.par(1,x)
    T=Ctx(M[:x]);A=C.o(r);mu,br,_=A;seed=T.o(r);D=dependencies(C,x);d=lift_counts(C,x,A)
    cnt['frames']+=1
    for i in range(x):
        if (False,i) in D and C.e12(i):
            W=C.bumpW(i)
            if ohole(W) and cof(W)[0]=='omega':
                for q in summ(C.vOpt1(i)):
                    if not lt(q,W):continue
                    cnt['aw.cases']+=1
                    bad=[m for m in range(MM) if m+d[i]>=1 and not lt(q,fsD(W,gamS(mu,br,seed,m+d[i])))]
                    if bad:
                        mx=max(bad);cnt['aw.maxm%d'%mx]+=1
                        cnt['aw.Wnode%d'%int(W==A)]+=1;cnt['aw.d%d'%d[i]]+=1
                        key='aw.m%d'%mx
                        if key not in ex or len(M)<ex[key][0]:ex[key]=(len(M),ms(M),'i=%d d=%d bad=%s WisA=%s'%(i,d[i],bad,W==A))
        if (True,i) in D:
            s,y,_=C.o(i)
            if y==br or split(y,(succ(s),Z,Z))[1]!=Z:continue
            l=last(y)
            if not l or l[1]!=Z:continue
            a=l[0]
            if isSucc(a) or not ohole(a) or cof(a)[0]!='omega':continue
            th=(succ(s),Z,Z);cnt['tp.cases']+=1
            bad=[m for m in range(MM) if m+d[i]>=1 and lt((fsD(a,gamS(mu,br,seed,m+d[i])),Z,Z),th)]
            if bad:
                mx=max(bad);cnt['tp.maxm%d'%mx]+=1;cnt['tp.aisA%d'%int(a==A)]+=1;cnt['tp.d%d'%d[i]]+=1
                key='tp.m%d'%mx
                if key not in ex or len(M)<ex[key][0]:ex[key]=(len(M),ms(M),'c=%d d=%d bad=%s aisA=%s'%(i,d[i],bad,a==A))
def work(batch):
    cnt=collections.Counter();ex={}
    for mm in batch:
        M=[tuple(c) for c in mm]
        try:meas(M,cnt,ex)
        except Exception as e:
            cnt['exc.'+type(e).__name__]+=1
            if 'exc' not in ex:ex['exc']=(len(M),ms(M),repr(e)[:300])
    return cnt,ex
if __name__=='__main__':
    npr=int(sys.argv[1]);out=open(sys.argv[2],'a')
    for f in sys.argv[3:]:
        t=time.time();mats=pickle.load(open(f,'rb'))
        cnt=collections.Counter();ex={}
        with Pool(npr) as pool:
            for c,e in pool.imap_unordered(work,(mats[i:i+200] for i in range(0,len(mats),200))):
                cnt.update(c)
                for k,v in e.items():
                    if k not in ex or v[0]<ex[k][0]:ex[k]=v
        out.write(json.dumps({'set':os.path.basename(f),'n':len(mats),'sec':round(time.time()-t),'cnt':dict(sorted(cnt.items())),'ex':ex})+'\n');out.flush()
