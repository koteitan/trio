"""Classify the last changing bump grandchild c of the last changing branch j
at every W-changing column i in Bad2 (a) frames. Cases (i)/(ii) of the codex
handoff. No head filter; head>=omega^2 recorded separately. Run nice15."""
import sys,json,pickle,time,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from pathlib import Path
from multiprocessing import Pool
from t2src_a_trio_codex import *
def anc0(C,a,d):
    while d is not None:
        if d==a:return True
        d=C.e.par(0,d)
    return False
def run(batch):
    cnt=collections.Counter();ex={}
    def save(tag,M,data):
        e=dict(matrix=M,matrix_text=mattext(M),**data)
        if tag not in ex or len(M)<len(ex[tag]['matrix']):ex[tag]=e
    for mm in batch:
        M=list(map(tuple,mm));x=len(M)-1
        if x<2 or M[x][2]!=1:continue
        E=Y.Ev(M);ku=E._upg[x-1]
        if ku is None:continue
        p=E.par(0,x-1);g=E.par(0,p) if p is not None else None
        if g is None or M[p]!=E.bump(g):continue
        C=Ctx(M);T=Ctx(M[:x])
        if not C.ok or not T.ok:continue
        if C.e.par(2,x) is None:continue
        if not (C.e.par(0,x)!=x-1 or C.e.par(1,x)!=x-1):continue
        upgabs,_,_=upgabs_all(C.vOpt1(x-1),C.v(ku))
        recs=[];bumpabs=True
        for i in range(x):
            if not C.e12(i):continue
            W=C.bumpW(i);WT=T.bumpW(i)
            if W==WT:continue
            V=C.vOpt1(i)
            raw=[q for q in H.summ(V) if not lt(q,WT) and lt(q,W)]
            if any(not lhd(q,W) for q in raw):bumpabs=False
            recs.append((i,V,W,WT))
        b2=(not upgabs) or (C.e.par(0,x)==x-1 and M[x][1]!=0 and not bumpabs)
        if not b2:continue
        cnt['A.matrices']+=1
        for i,V,W,WT in recs:
            cnt['Wchg']+=1
            lo=Y.split(V,W)[1];head=Z if not lo else (lo[0],lo[1],Z)
            big=not lt(head,W2)
            js=[j for j in T.ch(i) if C.bumpTerm(i,j)!=T.bumpTerm(i,j)]
            if not js:cnt['no_branch']+=1;continue
            j=js[-1];cs_=[c for c in T.ch(j) if C.o(c)!=T.o(c)]
            if not cs_:cnt['no_child']+=1;continue
            c=cs_[-1];m=C.e.par(1,i)
            if m!=C.e.par(0,i):cnt['m_ne']+=1;continue
            if c==x-1:cat='lost'
            elif M[c][1]>M[m][1]:cat='high'
            elif any(M[d][1]>=M[m][1] for d in T.ch(j) if d<c):cat='earlier'
            elif M[c][1]==M[m][1] and M[c+1][0]>M[m][0]:cat='nonlost_ret'
            elif M[c][1]==M[m][1]:cat='case_i'
            else:cat='case_ii'
            cnt[cat]+=1
            if big:cnt[cat+'.big']+=1
            if cat!='lost':
                cnt[cat+'.c1_in_i.'+str(anc0(C,i,c+1))]+=1;cnt[cat+'.c1_in_m.'+str(anc0(C,m,c+1))]+=1;cnt[cat+'.c1_child_of_m.'+str(C.e.par(0,c+1)==m)]+=1;cnt[cat+'.xm1_in_m.'+str(anc0(C,m,x-1))]+=1;cnt[cat+'.x_in_m.'+str(anc0(C,m,x))]+=1
            if cat!='lost':
                a=anc0(C,c,x-1)
                cnt[cat+'.anc_xm1.'+str(a)]+=1
                cnt[cat+'.leaf.'+str(not C.ch(c))]+=1
                cnt[cat+'.vchg.'+str(C.v(c)!=T.v(c))]+=1
                cnt[cat+'.A_le_newv.'+str(le(V,T.v(c)))]+=1
                cnt[cat+'.A_lt_newo.'+str(lt(V,T.o(c)))]+=1
                cnt[cat+'.upgc_next.'+str(C.upg(c)==c+1)]+=1
                cnt[cat+'.last_child_of_j_in_M.'+str(C.ch(j)[-1]==c)]+=1
                cnt[cat+'.window_nonempty.'+str(any(not lt(q,WT) and lt(q,W) and not lt(q,W2) for q in H.summ(V)))]+=1
                pass
            if cat!='lost':save(cat+('.big' if big else '.small'),M,dict(x=x,i=i,j=j,c=c,m=m,V=Y.tstr(V),W=Y.tstr(W),WT=Y.tstr(WT),vc=Y.tstr(C.v(c)),vcT=Y.tstr(T.v(c)),oc=Y.tstr(C.o(c)),ocT=Y.tstr(T.o(c))))
    return dict(cnt),ex
if __name__=='__main__':
    out=Path(sys.argv[1]);report={}
    with Pool(4) as pool:
        for src in sys.argv[2:]:
            p=Path(src)
            if not p.exists():p=SETD/(src+'.pkl')
            mats=pickle.load(p.open('rb'))
            if isinstance(mats,dict):mats=mats.get('seeds',[])+mats.get('ext',[])
            cnt=collections.Counter();ex={};t0=time.time()
            for cc,ee in pool.imap_unordered(run,(mats[i:i+50] for i in range(0,len(mats),50))):
                cnt.update(cc)
                for tag,e in ee.items():
                    if tag not in ex or len(e['matrix'])<len(ex[tag]['matrix']):ex[tag]=e
            report[src]=dict(n=len(mats),sec=round(time.time()-t0),counts=dict(cnt),examples=ex)
            out.write_text(json.dumps(report,indent=1)+'\n')
            print(json.dumps(dict(set=src,counts=dict(sorted(cnt.items())))),flush=True)
