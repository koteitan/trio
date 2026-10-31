"""Structural probe for the shared next-column case (B)/(O').
For last column x: i (e1,e2!=0, P0 i=P1 i=m), j last child of i below x, bump; c last child of j,
c<x-1, e1 c<=e1 m, earlier children of j e1<e1 m, c not anc of x-1, c' = next col after c subtree,
c'<x, upg(c'-1)=c', q=P0 c' strict anc of m.  Count with structural Bad2-lite levels:
 L0 none; L1 upg(x-1) exists; L2 + P0(x-1) bump child of its parent. Values (o change of c) only on hits."""
import sys,json,pickle,time,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from pathlib import Path
from multiprocessing import Pool
from t2src_a_trio_codex import *
from bad2_exact_trio_codex import bad2
def anc0(E,a,d):
    while d is not None:
        if d==a:return True
        d=E.par(0,d)
    return False
def hits(M,E,x):
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
        if anc0(E,c,x-1):continue
        cp=c+1
        while cp<=x and anc0(E,c,cp):cp+=1
        if cp>=x:continue
        if E._upg[cp-1]!=cp:continue
        q=E.par(0,cp)
        if q is None or q==m or not anc0(E,q,m):continue
        out.append((i,m,j,c,cp,q))
    return out
def run(batch):
    cnt=collections.Counter();ex={}
    def save(tag,M,data):
        e=dict(matrix_text=mattext(M),n=len(M),**data)
        if tag not in ex or len(M)<ex[tag]['n']:ex[tag]=e
    for mm in batch:
        M=list(map(tuple,mm));x=len(M)-1
        if x<3:continue
        cnt['input']+=1
        E=Y.Ev(M)
        hs=hits(M,E,x)
        if not hs:continue
        lv=0
        ku=E._upg[x-1]
        if ku is not None:
            lv=1
            p=E.par(0,x-1);g=E.par(0,p) if p is not None else None
            if g is not None and M[p]==E.bump(g):lv=2
        case='b' if (E.par(0,x)==x-1 and E.par(1,x)==x-1) else 'a'
        C=Ctx(M);T=Ctx(M[:x])
        if not C.ok or not T.ok:cnt['evalfail']+=1;continue
        b2=False
        if lv==2:
            try:b2=bad2(C,T)[0]
            except Exception as e:cnt['bad2err']+=1
        for h in hs:
            i,m,j,c,cp,q=h
            ch=C.o(c)!=T.o(c)
            df=None
            if ch:
                W=C.bumpW(i);WT=T.bumpW(i)
                df=any(not lt(s_,W2) and not lt(s_,WT) and lt(s_,W) and not lhd(s_,W) for s_ in H.summ(C.vOpt1(i)))
                g_=E.par(0,E.par(0,x-1)) if E.par(0,x-1) is not None else None
                cnt['chg.df%s.B2%s.cpg%s'%(df,b2,cp==g_)]+=1
                win=[s_ for s_ in H.summ(C.vOpt1(i)) if not lt(s_,W2) and not lt(s_,WT) and lt(s_,W)]
                small=[s_ for s_ in H.summ(C.vOpt1(i)) if lt(s_,W) and not lt(s_,W2)]
                cnt['win.%s.small%d.WTeqW%s'%('empty' if not win else 'lhd',min(len(small),3),WT==W)]+=1
                c1=le(C.v(m),T.v(c));c2=le(C.v(m),C.v(c))
                tg='cert.vm_le_vTc%s.vm_le_vc%s.e1c_eq_e1m%s.e1m_eq_e1q1%s'%(c1,c2,M[c][1]==M[m][1],M[m][1]==M[q][1]+1)
                cnt[tg]+=1
                save(tg,M,dict(i=i,m=m,j=j,c=c,cp=cp,q=q))
            tag='L%d.%s.chg%s.e2x%d.B2%s'%(lv,case,ch,M[x][2],b2)
            cnt[tag]+=1
            save(tag,M,dict(i=i,m=m,j=j,c=c,cp=cp,q=q,ku=ku))
    return dict(cnt),ex
if __name__=='__main__':
    out=Path(sys.argv[1]);report={}
    if out.exists():report=json.loads(out.read_text())
    with Pool(4) as pool:
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
