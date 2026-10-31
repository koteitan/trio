import sys,re
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from t2src_a_trio_codex import *
s=sys.argv[1];M=[tuple(map(int,t.split(','))) for t in re.findall(r'\(([^)]*)\)',s)]
x=len(M)-1;C=Ctx(M);T=Ctx(M[:x])
ku=C.upg(x-1);print('x',x,'upg(x-1)',ku,'UpgAbsX',upgabs_all(C.vOpt1(x-1),C.v(ku))[0] if ku is not None else None)
for i in range(x):
    if not C.e12(i):continue
    W=C.bumpW(i);WT=T.bumpW(i)
    if W==WT:continue
    V=C.vOpt1(i)
    win=[q for q in H.summ(V) if not lt(q,WT) and lt(q,W) and not lt(q,W2)]
    print('i',i,'P1',C.e.par(1,i),'V',Y.tstr(V),'W',Y.tstr(W),'WT',Y.tstr(WT),'win',[Y.tstr(q) for q in win],'fail',[Y.tstr(q) for q in win if not lhd(q,W)])
for c in map(int,sys.argv[2:]):
    print('c',c,'v',Y.tstr(C.v(c)),'vT',Y.tstr(T.v(c)),'o',Y.tstr(C.o(c)),'oT',Y.tstr(T.o(c)))
