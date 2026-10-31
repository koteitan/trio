"""AbsDN family probe (WfInvA, 2026-10-31).
usage: nice -n 15 python3 probe_adn.py NPROC PKL...
Fields (Lean forms):
 AbsDN      (V3QRFinal4) every i: e12 i, W=bumpW i, OHole W, cof W = omega, NotNode W; q in summands vOpt(P1 i), q<W -> q<fsD W 1
 AbsDN.fr   AbsDN restricted to the q=r last-column frame, i in D(false), i<x (eta 1)
 AbsDN0     cand: q=r frame (o r = psi_mu(b+Omega_{mu+1})), i<x, DepX false i, e12 i, dOf i = 0, OHole, cof omega, NotNode W, eta = seed
 AbsDN0x    as AbsDN0 without NotNode
 AbsDN0c    as AbsDN0 restricted to the consumer: W != psi_mu(b_r) (qr_lastNA) -- same as NotNode in practice; plus the bump case
 AbsDWs     (V3Inv2) q=r frame, D false, e12, OHole, cof omega, eta = gamS mu b_r seed (max 1 d_i)
 AbsDWs0    AbsDWs with k = d_i (k = 0 -> seed), no NotNode: AbsDWs and AbsDN0x together
 TPLoWs     (V3Inv2) q=r frame, D true c, ... eta = gamS mu b_r seed (max 1 d_c)
 TPLoN      (V3QRFinal4) d_c = 0, NotNode a, eta = seed
seed = o_{M.take x}(r).  Only M < SRO.
"""
import sys,os,pickle,json,collections,time
from multiprocessing import Pool
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from probe_inv2 import SRO, dependencies
from probe_trigs0 import lift_counts
from probe_inv3_prefix import Ctx, Z, ONE, cof, fs, fsD, isSucc, last, lt, notNode, ohole, split, succ, summ
def gamS(mu,b,seed,k):
    t=seed
    for _ in range(k):t=(mu,fs(b,t),Z)
    return t
def ms(M):return ''.join('(%d,%d,%d)'%tuple(c) for c in M)
def measure(M,cnt,ex):
    def note(f,ok,**info):
        cnt[f+'.cases']+=1
        if not ok:
            cnt[f+'.FAIL']+=1
            if f not in ex or len(M)<ex[f][0]:ex[f]=(len(M),ms(M),repr(info)[:700])
    if not M<SRO:cnt['outside_SRO']+=1;return
    C=Ctx(M)
    if not C.ok:cnt['eval_failed']+=1;return
    cnt['measured']+=1
    def absorb(f,i,W,eta,**kw):
        F=fsD(W,eta)
        for t in summ(C.vOpt1(i)):
            if lt(t,W):note(f,lt(t,F),i=i,q=t,W=W,eta=eta,**kw)
    for i in range(len(M)):
        if C.e12(i):
            W=C.bumpW(i)
            if ohole(W) and cof(W)[0]=='omega' and notNode(W):absorb('AbsDN',i,W,ONE)
    x=len(M)-1
    if x<1 or M[x][1]==0 or M[x][2]!=0:return
    r,q=C.e.par(1,x),C.e.par(0,x)
    if r is None or q!=r:return
    T=Ctx(M[:x])
    if not T.ok:cnt['seed_eval_failed']+=1;return
    A=C.o(r);mu,br,rest=A
    if rest!=Z or not br or last(br)!=(succ(mu),Z,Z):return
    seed=T.o(r);D=dependencies(C,x);d=lift_counts(C,x,A)
    cnt['frames']+=1
    FR.append(tuple(M))
    for i in range(x):
        if (False,i) in D and C.e12(i):
            W=C.bumpW(i)
            if ohole(W) and cof(W)[0]=='omega':
                nn=notNode(W)
                if nn:absorb('AbsDN.fr',i,W,ONE)
                absorb('AbsDWs',i,W,gamS(mu,br,seed,max(1,d[i])),d=d[i])
                absorb('AbsDWs0',i,W,gamS(mu,br,seed,d[i]),d=d[i])
                if d[i]==0:
                    absorb('AbsDN0x',i,W,seed,nn=nn)
                    if nn:absorb('AbsDN0',i,W,seed)
                    if W!=(mu,br,Z):absorb('AbsDN0c',i,W,seed)
        if (True,i) in D:
            s,y,_=C.o(i)
            if y==br or split(y,(succ(s),Z,Z))[1]!=Z:continue
            l=last(y)
            if not l or l[1]!=Z:continue
            a=l[0]
            if isSucc(a) or not ohole(a) or cof(a)[0]!='omega':continue
            th=(succ(s),Z,Z)
            note('TPLoWs',not lt((fsD(a,gamS(mu,br,seed,max(1,d[i]))),Z,Z),th),c=i)
            if d[i]==0 and notNode(a):note('TPLoN',not lt((fsD(a,seed),Z,Z),th),c=i)
def work(batch):
    global FR
    FR=[]
    cnt=collections.Counter();ex={}
    for mm in batch:
        M=[tuple(c) for c in mm]
        try:measure(M,cnt,ex)
        except Exception as e:
            cnt['exception.'+type(e).__name__]+=1
            if 'exception' not in ex:ex['exception']=(len(M),ms(M),repr(e)[:300])
    return cnt,ex,FR
def load(f):
    mats=pickle.load(open(f,'rb'))
    if isinstance(mats,dict):mats=mats['seeds']+mats['ext'] if 'seeds' in mats else list(mats.values())
    return mats
if __name__=='__main__':
    npr=int(sys.argv[1])
    for f in sys.argv[2:]:
        t=time.time();mats=load(f)
        cnt=collections.Counter();ex={}
        with Pool(npr) as pool:
            fr=[]
            for c,e,F in pool.imap_unordered(work,(mats[i:i+200] for i in range(0,len(mats),200))):
                cnt.update(c);fr+=F
                for k,v in e.items():
                    if k not in ex or v[0]<ex[k][0]:ex[k]=v
        pickle.dump(fr,open(os.environ.get('FRDIR','/home/koteitan/proofs/trio/tmp/wf/WfInvA/frames/')+os.path.basename(f),'wb'))
        print(json.dumps({'set':f.replace('/home/koteitan/proofs/trio/tmp/',''),'n':len(mats),'sec':round(time.time()-t),
          'cnt':dict(sorted(cnt.items())),'ex':ex}),flush=True)
