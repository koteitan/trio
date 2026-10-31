"""Classify every row-1 chain column b of m (b = m, P1 m, ...) with upg b = k by
lo = e1 b < e1 c, chg = v(b) changes in M.take x, via = a bump child of k is an ancestor of m,
and the term t = last v(k): geW / ltWT / small / lhd / BAD.  Also whether t is a surviving summand of v(m)."""
import sys,json,pickle,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfSrcO')
from t2src_a_trio_codex import *
from bad2_exact_trio_codex import lhd
from probe_B import hits,anc0
cnt=collections.Counter();ex={}
mats=pickle.load(open(sys.argv[1],'rb'))
for M in mats:
    x=len(M)-1;E=Y.Ev(M);C=Ctx(M);T=Ctx(M[:x])
    for (i,m,j,c,cp,q) in hits(M,E,x):
        if C.o(c)==T.o(c):continue
        W=C.bumpW(i);WT=T.bumpW(i);sm=H.summ(C.v(m))
        b=m
        while b is not None:
            k=E._upg[b]
            if k is not None:
                t=Y.last(C.v(k))
                if le(W,t):tg='geW'
                elif lt(t,WT):tg='ltWT'
                elif lt(t,W2):tg='small'
                elif lhd(t,W):tg='lhd'
                else:tg='BAD'
                lo=M[b][1]<M[c][1];ch=C.v(b)!=T.v(b)
                via=any(M[l]==E.bump(k) and anc0(E,l,m) for l in E.children[k])
                tag='%s.lo%s.chg%s.via%s.aboveq%s.surv%s'%(tg,lo,ch,via,b>q,t in sm)
                cnt[tag]+=1
                if tag not in ex or len(M)<ex[tag][1]:ex[tag]=(mattext(M),len(M),dict(i=i,m=m,c=c,q=q,b=b,k=k))
            b=E.par(1,b)
for k_ in sorted(cnt):print(cnt[k_],k_)
json.dump(ex,open(sys.argv[2],'w'),indent=1)
