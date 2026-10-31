"""Gap claim on case-(b) non-lost lower-row frames: for b on the row-1 chain of m, k = upg b < i,
j0 bump child of k, d child of j0:  o(d) < oT(c)  or  o(c) <= o(d).  All frames (not only DropFail)."""
import collections,json,pickle,sys,time
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
    def save(tag,C,data):
        e=dict(matrix_text=mattext(C.M),n=len(C.M),**data)
        if tag not in ex or len(C.M)<ex[tag]['n']:ex[tag]=e
    for mm in batch:
        M=list(map(tuple,mm));x=len(M)-1
        if x<2 or M[x][2]!=1:continue
        E=Y.Ev(M)
        if E.par(0,x)!=x-1 or E.par(1,x)!=x-1 or E._upg[x-1] is None:continue
        C=Ctx(M)
        if not C.ok:continue
        p=C.e.par(0,x-1);g=C.e.par(0,p) if p is not None else None
        if g is None or M[p]!=C.e.bump(g):continue
        T=Ctx(M[:x])
        if not T.ok:continue
        for i in range(x):
            if not C.e12(i):continue
            if C.bumpW(i)==T.bumpW(i):continue
            m=C.e.par(1,i)
            if m is None or C.e.par(0,i)!=m:continue
            for j in T.ch(i):
                if M[j]!=C.e.bump(i):continue
                cs=[c for c in T.ch(j) if C.o(c)!=T.o(c)]
                for c in cs:
                    if c==x-1:continue
                    desc=anc0(C,c,x-1)
                    kind=('P' if desc and M[c][1]<M[m][1] else 'Pret' if desc else
                          'Ohigh' if M[c][1]>M[m][1] else 'Olow')
                    for scope in ('all',):
                        b=m;ok=True;n=0
                        while b is not None:
                            k=C.upg(b)
                            if k is not None and k<i:
                                for j0 in C.ch(k):
                                    if M[j0]!=C.e.bump(k):continue
                                    for d in C.ch(j0):
                                        n+=1
                                        good=lt(C.o(d),T.o(c)) or le(C.o(c),C.o(d))
                                        cnt[kind+'.pairs']+=1
                                        cnt[kind+'.pairs.j0lt_i.'+str(j0<i)]+=1
                                        if not good:
                                            ok=False;cnt[kind+'.VIOL.j0lt_i.'+str(j0<i)]+=1
                                            save(kind+'.VIOL',C,dict(x=x,i=i,j=j,c=c,m=m,b=b,k=k,j0=j0,d=d,od=Y.tstr(C.o(d)),oc=Y.tstr(C.o(c)),ocT=Y.tstr(T.o(c))))
                            b=C.e.par(1,b)
                        cnt[kind+'.frames']+=1
                        cnt[kind+'.frames.ok']+=ok
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
