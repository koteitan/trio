"""Case (b) of T2AbsNSrcW: P0 x = P1 x = x-1. Classify changing bump grandchildren c at W-changing e12 columns.
Run from trio root, nice15, PYTHONPATH=tmp/codex:tools."""
import collections,json,pickle,sys,time
from pathlib import Path
from multiprocessing import Pool
from t2src_a_trio_codex import *

def anc1(C,m,d):
    seen=set()
    while d is not None and d not in seen:
        if d==m:return True
        seen.add(d);d=C.e.par(1,d)
    return False
def anc0(C,a,d):
    while d is not None:
        if d==a:return True
        d=C.e.par(0,d)
    return False
def run(batch):
    cnt=collections.Counter();ex={}
    def save(tag,C,data):
        e=dict(matrix_text=mattext(C.M),n=len(C.M),**data)
        if tag not in ex or len(C.M)<ex[tag]['n']:ex[tag]=e
    for mm in batch:
        cnt['input']+=1;M=list(map(tuple,mm));x=len(M)-1
        if x<2 or M[x][2]!=1:continue
        C=Ctx(M)
        if not C.ok:continue
        if C.e.par(0,x)!=x-1 or C.e.par(1,x)!=x-1:continue
        k=C.upg(x-1)
        if k is None:continue
        p=C.e.par(0,x-1);g=C.e.par(0,p) if p is not None else None
        if g is None or M[p]!=C.e.bump(g):continue
        T=Ctx(M[:x])
        if not T.ok:continue
        cnt['B.frames']+=1
        cnt['B.r_is_prev']+=C.e.par(2,x)==x-1
        for i in range(x):
            if not C.e12(i):continue
            W=C.bumpW(i);WT=T.bumpW(i)
            if W==WT:continue
            cnt['Wchg']+=1
            V=C.vOpt1(i)
            raw=[q for q in H.summ(V) if not lt(q,WT) and lt(q,W) and not lt(q,W2)]
            fail=any(not lhd(q,W) for q in raw)
            cnt['Wchg.fail']+=fail
            cnt['Wchg.fail.i_is_g']+=fail and i==g
            m=C.e.par(1,i)
            for j in T.ch(i):
                if C.bumpTerm(i,j)==T.bumpTerm(i,j):continue
                cs=[c for c in T.ch(j) if C.o(c)!=T.o(c)]
                for c in cs:
                    tag='lost' if c==x-1 else None
                    if tag is None:
                        earlier=[d for d in T.ch(j) if d<c]
                        returns=[d for d in earlier if M[d][1]==M[m][1] and M[d][2]==0 and M[m][2]==0 and C.e.par(0,i)==m]
                        tag=('high' if M[c][1]>M[m][1] else 'earlier_return' if returns else
                             'nonlost_return' if M[c][1]==M[m][1] and c+1<x and M[c+1][0]>M[m][0] else
                             'row1_desc' if anc1(C,m,c) else 'pending')
                    desc=anc0(C,c,x-1)
                    key='%s.%s.%s'%(tag,'fail' if fail else 'ok','prevdesc' if desc else 'outside')
                    cnt['c.'+key]+=1
                    if tag=='pending':
                        cnt['pending.c_eq_p']+=c==p
                        cnt['pending.i_eq_g']+=i==g
                        cnt['pending.e1c_eq_e1m']+=M[c][1]==M[m][1]
                        save('pending.'+('prevdesc' if desc else 'outside'),C,dict(x=x,i=i,j=j,c=c,m=m,p=p,g=g,k=k,V=Y.tstr(V),W=Y.tstr(W),WT=Y.tstr(WT),oc=Y.tstr(C.o(c)),ocT=Y.tstr(T.o(c))))
                    if fail and tag!='lost':save('FAILnonlost',C,dict(x=x,i=i,j=j,c=c,tag=tag))
    return dict(cnt),ex

if __name__=='__main__':
    start=time.time();report={};out=Path(sys.argv[1])
    with Pool(4) as pool:
        for src in sys.argv[2:]:
            if src=='grow':
                sys.path.insert(0,'tmp/wf/WfT2Abs');import probe_sets;mats=probe_sets.grow()
            else:
                p=Path(src)
                if not p.exists():p=SETD/(src+'.pkl')
                mats=pickle.load(p.open('rb'))
            if isinstance(mats,dict):mats=mats['seeds']+mats['ext']
            cnt=collections.Counter();ex={}
            for cc,ee in pool.imap_unordered(run,(mats[i:i+50] for i in range(0,len(mats),50))):
                cnt.update(cc)
                for tag,e in ee.items():
                    if tag not in ex or e['n']<ex[tag]['n']:ex[tag]=e
            report[src]=dict(input=len(mats),counts=dict(cnt),examples=ex)
            out.write_text(json.dumps(dict(seconds=round(time.time()-start,2),sets=report),indent=2)+'\n')
            print(json.dumps(dict(set=src,counts=dict(cnt))),flush=True)
