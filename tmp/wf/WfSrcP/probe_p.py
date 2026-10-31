"""Lower-row case P: c bump grandchild of i (j bump child), c changes, c < x-1 ancestor of x-1,
e1 c < e1 m (m = P0 i = P1 i). Measure value facts.
Run from trio root: nice -n 15 env PYTHONPATH=tmp/codex:tools python3 tmp/wf/WfSrcP/probe_p.py OUT sets..."""
import collections,json,pickle,sys,time
from pathlib import Path
from multiprocessing import Pool
from t2src_a_trio_codex import *
from bad2_exact_trio_codex import lhd,upgabs_all

def anc0(C,a,d):
    while d is not None:
        if d==a:return True
        if d<a:return False
        d=C.e.par(0,d)
    return False
def lev(t):return Z if t==Z else t[0]
def hd(t):return Z if t==Z else (t[0],t[1],Z)
def run(batch):
    cnt=collections.Counter();ex={}
    def save(tag,M,data):
        e=dict(matrix_text=mattext(M),n=len(M),**data)
        if tag not in ex or len(M)<ex[tag]['n']:ex[tag]=e
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
        case='b' if (C.e.par(0,x)==x-1 and C.e.par(1,x)==x-1) else 'a'
        Vprev=C.vOpt1(x-1)
        upgabs,_,_=upgabs_all(Vprev,C.v(ku))
        recs=[]
        for i in range(x):
            if not C.e12(i):continue
            W=C.bumpW(i);WT=T.bumpW(i)
            if W==WT:continue
            m=C.e.par(1,i)
            if m is None or C.e.par(0,i)!=m:continue
            recs.append((i,m,W,WT))
        bumpabs=True
        for i,m,W,WT in recs:
            V=C.vOpt1(i)
            if any(not lt(q,WT) and lt(q,W) and not lhd(q,W) for q in H.summ(V)):bumpabs=False
        b2=(not upgabs) or (C.e.par(0,x)==x-1 and M[x][1]!=0 and not bumpabs)
        tag0=case+('.B2' if b2 else '.nB2')
        cnt[tag0+'.frames']+=1
        for i,m,W,WT in recs:
            V=C.vOpt1(i)
            for j in T.ch(i):
                if M[j]!=C.e.bump(i) or C.bumpTerm(i,j)==T.bumpTerm(i,j):continue
                for c in T.ch(j):
                    if C.o(c)==T.o(c) or not c<x-1 or not anc0(C,c,x-1) or not M[c][1]<M[m][1]:continue
                    t=tag0+'.pre'
                    cnt[t]+=1
                    f1=T.ch(i)[-1]!=j;f2=C.ch(j)[-1]!=c
                    f3=any(C.bumpTerm(i,d)!=T.bumpTerm(i,d) for d in T.ch(i) if d!=j)
                    f4=any(C.o(d)!=T.o(d) for d in C.ch(j) if d!=c)
                    f5=any(M[d][1]>=M[m][1] for d in C.ch(j) if d!=c)
                    for nm,f in (('jnotlast',f1),('cnotlast',f2),('Bchg',f3),('Kchg',f4),('Khigh',f5)):cnt[t+'.'+nm]+=f
                    if f1 or f2 or f3 or f4 or f5:
                        if not (f1 or f2 or f3 or f4):save(t+'.onlyKhigh',M,dict(x=x,i=i,j=j,c=c,m=m,chj=C.ch(j)))
                        continue
                    t=tag0+'.P'
                    cnt[t]+=1
                    if not lt(C.v(m),T.o(c)):
                        r=t+'.RES'
                        cnt[r]+=1
                        cnt[r+'.e1c=%d'%M[c][1]]+=1
                        cnt[r+'.e1m-e1c=%d'%(M[m][1]-M[c][1])]+=1
                        cnt[r+'.nK=%d'%(len(C.ch(j))-1)]+=1
                        cnt[r+'.nB=%d'%(len(T.ch(i))-1)]+=1
                        cnt[r+'.Vsingle']+=len(H.summ(C.v(m)))==1
                        Wl=lev(C.bumpW(i));Vl=lev(hd(C.v(m)))
                        cnt[r+'.levV_gt_levW']+=lt(Wl,Vl)
                        cnt[r+'.levV_eq_levW']+=Wl==Vl
                        cnt[r+'.V_ge_W']+=not lt(C.v(m),C.bumpW(i))
                        cnt[r+'.V_lt_WT']+=lt(C.v(m),T.bumpW(i))
                        cnt[r+'.c_eq_Pg']+=C.e.par(0,g)==c
                        cnt[r+'.c_eq_PPg']+=C.e.par(0,C.e.par(0,g))==c
                    oc=C.o(c);ocT=T.o(c);vc=C.v(c);vcT=T.v(c)
                    cnt[t+'.vc_eq_vcT']+=vc==vcT
                    cnt[t+'.c_anc_g']+=anc0(C,c,g)
                    cnt[t+'.c_eq_Pg']+=C.e.par(0,g)==c
                    cnt[t+'.V_ge_W']+=not lt(V,W)
                    cnt[t+'.lastj']+=j==T.ch(i)[-1]
                    cnt[t+'.lastc']+=c==T.ch(j)[-1]
                    cnt[t+'.V_lt_ocT']+=lt(V,ocT)
                    cnt[t+'.V_lt_oc']+=lt(V,oc)
                    win=[q for q in H.summ(V) if not lt(q,WT) and lt(q,W) and not lt(q,W2)]
                    big=[q for q in H.summ(V) if not lt(q,ocT)]
                    if big:cnt[t+'.has_ge_ocT']+=1
                    for q in big:
                        cnt[t+'.big']+=1
                        cnt[t+'.big.lev_eq_vcT']+=lev(q)==vcT
                        cnt[t+'.big.lev_eq_vc']+=lev(q)==vc
                        cnt[t+'.big.lt_oc']+=lt(q,oc)
                        cnt[t+'.big.lhd_oc']+=lt(q,oc) and lhd(q,oc)
                        cnt[t+'.big.lhd_W']+=lt(q,W) and lhd(q,W)
                        cnt[t+'.big.ge_WT']+=not lt(q,WT)
                        cnt[t+'.big.ge_W2']+=not lt(q,W2)
                        cnt[t+'.big.is_head']+=q==hd(V)
                        if lev(q)==vc and q[0:1]==oc[0:1]:
                            cnt[t+'.big.argA_lt_argB']+=lt(q[1],oc[1])
                            cnt[t+'.big.argA_lhd_argB']+=lt(q[1],oc[1]) and lhd(q[1],oc[1])
                        cls='ltWT' if lt(q,WT) else ('geW' if not lt(q,W) else 'win')
                        cnt[t+'.cls.'+cls]+=1
                        cnt[t+'.cls.'+cls+'.ltW2']+=lt(q,W2)
                        cnt[t+'.cls.'+cls+'.lev_eq_vc']+=lev(q)==vc
                        cnt[t+'.cls.'+cls+'.lev_lt_vc']+=lt(lev(q),vc)
                        save(t+'.cls.'+cls,M,dict(x=x,i=i,j=j,c=c,m=m,g=g,p=p,q=Y.tstr(q),V=Y.tstr(V),oc=Y.tstr(oc),ocT=Y.tstr(ocT),W=Y.tstr(W),WT=Y.tstr(WT),vc=Y.tstr(vc),chi=T.ch(i),chj=T.ch(j)))
                        save(t+'.big',M,dict(x=x,i=i,j=j,c=c,m=m,q=Y.tstr(q),V=Y.tstr(V),oc=Y.tstr(oc),ocT=Y.tstr(ocT),W=Y.tstr(W),WT=Y.tstr(WT),vc=Y.tstr(vc),vcT=Y.tstr(vcT)))
                    if win:
                        cnt[t+'.win']+=1
                        save(t+'.win',M,dict(x=x,i=i,j=j,c=c,m=m,V=Y.tstr(V),oc=Y.tstr(oc),ocT=Y.tstr(ocT),W=Y.tstr(W),WT=Y.tstr(WT)))
                    if any(not lhd(q,W) for q in win):
                        cnt[t+'.FAIL']+=1
                        save(t+'.FAIL',M,dict(x=x,i=i,j=j,c=c,m=m))
    return dict(cnt),ex

if __name__=='__main__':
    start=time.time();report={};out=Path(sys.argv[1])
    with Pool(4) as pool:
        for src in sys.argv[2:]:
            if src=='grow':
                sys.path.insert(0,'tmp/wf/WfT2Abs');import probe_sets;mats=probe_sets.grow()
            else:
                pth=Path(src)
                if not pth.exists():pth=SETD/(src+'.pkl')
                mats=pickle.load(pth.open('rb'))
            if isinstance(mats,dict):mats=mats['seeds']+mats['ext']
            cnt=collections.Counter();ex={}
            for cc,ee in pool.imap_unordered(run,(mats[i:i+50] for i in range(0,len(mats),50))):
                cnt.update(cc)
                for tag,e in ee.items():
                    if tag not in ex or e['n']<ex[tag]['n']:ex[tag]=e
            report[src]=dict(input=len(mats),counts=dict(sorted(cnt.items())),examples=ex)
            out.write_text(json.dumps(dict(seconds=round(time.time()-start,2),sets=report),indent=2)+'\n')
            print(json.dumps(dict(set=src,counts=dict(sorted(cnt.items())))),flush=True)
