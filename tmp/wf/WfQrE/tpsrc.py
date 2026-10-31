"""TPLoQ (WfQrE): the (L)(ii) condition with the re-exposed summands.
Pattern (as TPLoW): q=r frame, D o-call c, o(c) = psi_s(y), y != b_r, split(y, Om_{s+1}).2 = 0, last y = psi_a(0),
a not succ, OHole a, cof a = omega.  Sources: D v-calls i with v(i) = a and a W (bump: bumpW i; upgrade: last v(upg i))
with v(i) = add(P, W), P = v(P1 i).  For m = 0..2, k = m + d_i:
  TPLoW(m)  : not psi(fsD(a, g_k)) < Om_{s+1}
  TPLoQ(m)  : not psi(add(P, fsD(W, g_k))) < Om_{s+1}         (the DQ value of a)
  PgeS      : s <= P  (then TPLoQ holds: add(P, W') > P >= s)
usage: nice -n 15 python3 tpsrc.py NPROC OUT.jsonl PKL..."""
import sys,os,pickle,json,collections,time
from multiprocessing import Pool
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvA')
from probe_adn import gamS, dependencies, lift_counts, Ctx, Z, fsD, summ, lt, ohole, cof, last, split, succ, isSucc, ms
from probe_inv3_prefix import le
import ytosk_eval as Y
def meas(M,cnt,ex):
    C=Ctx(M)
    if not C.ok:return
    x=len(M)-1;r=C.e.par(1,x);T=Ctx(M[:x]);A=C.o(r);mu,br,_=A;seed=T.o(r);D=dependencies(C,x);d=lift_counts(C,x,A)
    def note(k,ok,info):
        cnt[k+'.cases']+=1
        if not ok:
            cnt[k+'.FAIL']+=1
            if k not in ex or len(M)<ex[k][0]:ex[k]=(len(M),ms(M),info)
    for c in range(x):
        if (True,c) not in D:continue
        s,y,_=C.o(c)
        if not y or y==br or split(y,(succ(s),Z,Z))[1]!=Z:continue
        l=last(y)
        if not l or l[1]!=Z:continue
        a=l[0]
        if isSucc(a) or not ohole(a) or cof(a)[0]!='omega':continue
        th=(succ(s),Z,Z)
        tpw=[not lt((fsD(a,gamS(mu,br,seed,m+d[c])),Z,Z),th) for m in range(3)]
        srcs=[]
        for i in range(x):
            if (False,i) in D and C.v(i)==a and M[i][1]:
                if C.e12(i):W=C.bumpW(i)
                elif C.upg(i) is not None:W=last(C.v(C.upg(i)))
                else:continue
                srcs.append((i,C.vOpt1(i),W))
        cnt['pat']+=1;cnt['pat.nsrc%d'%min(len(srcs),3)]+=1
        failw=not all(tpw)
        if failw:cnt['tpw.fail']+=1
        if not srcs:
            if failw:note('nosrc_fail',False,'c=%d'%c)
            continue
        for (i,P,W) in srcs:
            tq=[not lt((Y.sf(Y.add(P,fsD(W,gamS(mu,br,seed,m+d[i])))),Z,Z),th) for m in range(3)]
            note('TPLoQ',all(tq),'c=%d i=%d d_c=%d d_i=%d tq=%s'%(c,i,d[c],d[i],tq))
            note('PgeS',le(s,P),'c=%d i=%d'%(c,i))
            if failw:
                note('TPLoQ_onfail',all(tq),'c=%d i=%d d_c=%d d_i=%d tq=%s'%(c,i,d[c],d[i],tq))
                note('PgeS_onfail',le(s,P),'c=%d i=%d'%(c,i))
            cnt['dsame%d'%int(d[i]==d[c])]+=1
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
