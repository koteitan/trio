"""Exact test of the residual WfSrcA.SrcAShape.
For the last column x (any matrix, variant V0) and additionally under the
Bad2 (a) frame (V1): i with e1,e2!=0, P0 i=P1 i=m; j bump child of i and the
last child of i below x; c last child of j (in M), c<x-1, o_T(c)!=o_M(c),
every earlier child of j has row1<e1 m, e1 c<=e1 m  ==>  e1 c=e1 m and
e0 m<e0(c+1).  Structural prefilter first, values only on candidates. nice15."""
import sys,json,pickle,time,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from pathlib import Path
from multiprocessing import Pool
from t2src_a_trio_codex import *
def anc0(E,a,d):
    while d is not None:
        if d==a:return True
        d=E.par(0,d)
    return False
def cands(M,E,x):
    out=[]
    for i in range(x):
        if M[i][1]==0 or M[i][2]==0:continue
        m=E.par(0,i)
        if m is None or E.par(1,i)!=m:continue
        chT=[d for d in E.children[i] if d<x]
        if not chT:continue
        j=chT[-1]
        if M[j]!=E.bump(i):continue
        ch=E.children[j]
        if not ch:continue
        c=ch[-1]
        if not c<x-1:continue
        if any(M[d][1]>=M[m][1] for d in ch[:-1]):continue
        if M[c][1]>M[m][1]:continue
        out.append((i,m,j,c))
    return out
def run(batch):
    cnt=collections.Counter();ex={}
    def save(tag,M,data):
        e=dict(matrix_text=mattext(M),n=len(M),**data)
        if tag not in ex or len(M)<ex[tag]['n']:ex[tag]=e
    for mm in batch:
        M=list(map(tuple,mm));x=len(M)-1
        if x<2:continue
        cnt['input']+=1
        E=Y.Ev(M)
        cs_=cands(M,E,x)
        if not cs_:continue
        frame=False;shape=False
        if M[x][2]==1 and E.par(2,x) is not None:
            ku=E._upg[x-1]
            if ku is not None and ku<x-1 and (E.par(0,x)!=x-1 or E.par(1,x)!=x-1):
                pp=E.par(0,x-1);gg=E.par(0,pp) if pp is not None else None
                shape=gg is not None and M[pp]==E.bump(gg)
                frame=None
        C=Ctx(M);T=Ctx(M[:x])
        if not C.ok or not T.ok:cnt['eval_fail']+=1;continue
        if frame is None:
            ku=E._upg[x-1];ua,_,_=upgabs_all(C.vOpt1(x-1),C.v(ku));frame=not ua
            # Bad2 second disjunct needs P0 x=x-1 with P1 x!=x-1; check BumpAbsC exactly
            if not frame and E.par(0,x)==x-1 and M[x][1]!=0:
                for i in range(x):
                    if not C.e12(i):continue
                    W=C.bumpW(i);WT=T.bumpW(i)
                    if W==WT:continue
                    if any(not lt(q,WT) and lt(q,W) and not lhd(q,W) for q in H.summ(C.vOpt1(i))):frame=True;break
        for (i,m,j,c) in cs_:
            if C.o(c)==T.o(c):continue
            ok=M[c][1]==M[m][1] and M[m][0]<M[c+1][0]
            for v in ['V0']+(['V1'] if frame else [])+(['V2'] if shape else []):
                cnt[v+'.antecedent']+=1
                if not ok:
                    cnt[v+'.FALSE']+=1
                    W=C.bumpW(i);WT=T.bumpW(i)
                    df=any(not lt(q,W2) and not lt(q,WT) and lt(q,W) and not lhd(q,W) for q in H.summ(C.vOpt1(i)))
                    cnt[v+'.FALSE.dropfail.'+str(df)]+=1
                    A=C.vOpt1(i);lo=Y.split(A,W)[1];head=Z if not lo else (lo[0],lo[1],Z)
                    cert=('A_le_newv' if le(A,T.v(c)) else 'A_lt_newo' if lt(A,T.o(c)) else 'head_small' if lt(head,W2) else 'head_lt_WT' if lt(head,WT) else 'other')
                    cnt[v+'.FALSE.cert.'+cert]+=1
                    cnt[v+'.FALSE.anc.'+str(anc0(E,c,x-1))+'.e1lt.'+str(M[c][1]<M[m][1])]+=1
                    if cert=='other':save(v+'.FALSE.other',M,dict(x=x,i=i,m=m,j=j,c=c))
                    if df:save(v+'.FALSE.DROPFAIL',M,dict(x=x,i=i,m=m,j=j,c=c))
                    save(v+'.FALSE',M,dict(x=x,i=i,m=m,j=j,c=c))
                else: save(v+'.true',M,dict(x=x,i=i,m=m,j=j,c=c))
    return dict(cnt),ex
if __name__=='__main__':
    out=Path(sys.argv[1]);report={}
    if out.exists():report=json.loads(out.read_text())
    with Pool(4) as pool:
        for src in sys.argv[2:]:
            p=Path(src)
            if not p.exists():p=SETD/(src+'.pkl')
            mats=pickle.load(p.open('rb'))
            if isinstance(mats,dict):mats=mats.get('seeds',[])+mats.get('ext',[])
            cnt=collections.Counter();ex={};t0=time.time()
            for cc,ee in pool.imap_unordered(run,(mats[i:i+200] for i in range(0,len(mats),200))):
                cnt.update(cc)
                for t,e in ee.items():
                    if t not in ex or e['n']<ex[t]['n']:ex[t]=e
            report[src]=dict(n=len(mats),sec=round(time.time()-t0),counts=dict(cnt),examples=ex)
            out.write_text(json.dumps(report,indent=1)+'\n')
            print(json.dumps(dict(set=src,sec=round(time.time()-t0),counts=dict(sorted(cnt.items())))),flush=True)
