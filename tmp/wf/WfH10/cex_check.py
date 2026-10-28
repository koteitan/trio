import sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import probe_inv3_prefix as P
import huac_structure_trio_codex as H
from huac_structure_trio_codex import Y,lt,summ,Z
import t0_h8_f3_trio_codex as F
from lhd_exact import lhd
s=sys.argv[1]
M=[tuple(map(int,t.split(','))) for t in s.strip('()').split(')(')]
cnt,ex=P.check(M)
print({k:v for k,v in cnt.items() if isinstance(k,tuple) and k[1]=='FAIL'})
for k,v in ex.items():
  if k[1]=='FAIL':print(k,[i[1:] for i in v])
C=H.Ctx(M);x=len(M)-1;k=C.upg(x-1);V=C.vOpt1(x-1);W=C.bumpW(k)
print('x',x,'k',k,'P1(x-1)',C.e.par(1,x-1),'V',Y.tstr(V),'W',Y.tstr(W),'v(k)',Y.tstr(C.v(k)),'strong',F.strong(C,x))
for q in summ(V):print(' q',Y.tstr(q),'q<W',lt(q,W),'lhd',lhd(q,W))
for i in range(len(M)):print(i,M[i],'p0',C.e.par(0,i),'p1',C.e.par(1,i),'upg',C.upg(i),'v',Y.tstr(C.v(i)),'o',Y.tstr(C.o(i)))
