"""WfTerm: value split at the next-column frame. Frames of probe_B (WfSrcO) with c changing.
For each: q (first chain step) and the row-1 chain of m down to q.
V1: v(q) < W_T(i) (M value of q).  V3: every chain upgrade b strictly above q (q < b <= m) with target k:
t = last v(k) satisfies t >= W(i) or t < W_T(i) or t < psi(2) or lhd(t,W)."""
import sys,json,pickle,time,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfSrcO')
from pathlib import Path
from multiprocessing import Pool
from t2src_a_trio_codex import *
from bad2_exact_trio_codex import bad2,lhd
from probe_B import hits,anc0
def run(batch):
    cnt=collections.Counter();ex={}
    def save(tag,M,data):
        e=dict(matrix_text=mattext(M),n=len(M),**data)
        if tag not in ex or len(M)<ex[tag]['n']:ex[tag]=e
    for mm in batch:
        M=list(map(tuple,mm));x=len(M)-1
        if x<3:continue
        E=Y.Ev(M)
        hs=hits(M,E,x)
        if not hs:continue
        C=Ctx(M);T=Ctx(M[:x])
        if not C.ok or not T.ok:continue
        case='b' if (E.par(0,x)==x-1 and E.par(1,x)==x-1) else 'a'
        for (i,m,j,c,cp,q) in hs:
            if C.o(c)==T.o(c):continue
            W=C.bumpW(i);WT=T.bumpW(i)
            ch=[];a=m;ok=True
            while a!=q:
                ch.append(a);a=E.par(1,a)
                if a is None or a<q:ok=False;break
            cnt['reach%s'%ok]+=1
            if not ok:save('noreach',M,dict(i=i,m=m,c=c,q=q));continue
            v1=lt(C.v(q),WT);v1T=lt(T.v(q),WT);cnt['V1.%s.T%s'%(v1,v1T)]+=1
            if not v1:save('V1false',M,dict(i=i,m=m,c=c,q=q))
            for b in ch:
                k=E._upg[b]
                if k is None:continue
                t=Y.last(C.v(k))
                if le(W,t):tg='geW'
                elif lt(t,WT):tg='ltWT'
                elif lt(t,W2):tg='small'
                elif lhd(t,W):tg='lhd'
                else:tg='BAD'
                cnt['V3.'+tg]+=1
                save('V3.'+tg,M,dict(i=i,m=m,c=c,q=q,b=b,k=k))
                if tg=='BAD':cnt['V3BAD.'+case]+=1
            for s_ in H.summ(C.v(m)):
                if lt(s_,W) and not lt(s_,W2):
                    cnt['sumlt.%s'%('leq' if le(s_,C.v(q)) else 'gtq')]+=1
    return dict(cnt),ex
if __name__=='__main__':
    out=Path(sys.argv[1]);report={}
    if out.exists():report=json.loads(out.read_text())
    with Pool(3) as pool:
        for src in sys.argv[2:]:
            p=Path(src)
            if not p.exists():p=Path('/home/koteitan/proofs/trio/tmp/ytosk-handoff/sets')/(src+'.pkl')
            mats=pickle.load(p.open('rb'))
            if isinstance(mats,dict):mats=mats.get('seeds',[])+mats.get('ext',[])
            cnt=collections.Counter();ex={};t0=time.time()
            for cc,ee in pool.imap_unordered(run,(mats[i:i+500] for i in range(0,len(mats),500))):
                cnt.update(cc)
                for t,e in ee.items():
                    if t not in ex or e['n']<ex[t]['n']:ex[t]=e
            report[src]=dict(n=len(mats),sec=round(time.time()-t0),counts=dict(cnt),examples=ex)
            out.write_text(json.dumps(report,indent=1)+'\n')
            print(json.dumps(dict(set=src,sec=round(time.time()-t0),counts=dict(sorted(cnt.items())))),flush=True)
