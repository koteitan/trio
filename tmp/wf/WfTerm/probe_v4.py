import sys,json,pickle,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfSrcO')
from t2src_a_trio_codex import *
from probe_B import hits,anc0
cnt=collections.Counter()
for M in pickle.load(open(sys.argv[1],'rb')):
    x=len(M)-1;E=Y.Ev(M);C=Ctx(M);T=Ctx(M[:x])
    for (i,m,j,c,cp,q) in hits(M,E,x):
        if C.o(c)==T.o(c):continue
        W=C.bumpW(i);WT=T.bumpW(i)
        cnt['P1c=q %s'%(E.par(1,c)==q)]+=1
        cnt['oc<W %s, WT<=oc? %s'%(lt(C.o(c),W), le(WT,C.o(c)))]+=1
        b=m
        while b is not None and b>q:
            k=E._upg[b]
            if k is not None:
                t=Y.last(C.v(k));tg='geW' if le(W,t) else ('ltWT' if lt(t,WT) else 'BAD')
                lv=t[0]  # psi index of t (t = psi lv ...)
                cnt['%s le_vTc=%s gt_vc=%s ge_oc=%s lt_oTc=%s idx<=vq=%s idx>vc=%s'%(tg,le(t,T.v(c)),lt(C.v(c),t),le(C.o(c),t),lt(t,T.o(c)),le(lv,C.v(q)),lt(C.v(c),lv))]+=1
            b=E.par(1,b)
for k_ in sorted(cnt):print(cnt[k_],k_)
