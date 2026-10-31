import sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from stepfacts3_core_trio_codex import *
from bad2_exact_trio_codex import bad2,upgabs_all
from lhd_exact import comps,tmax
import ytosk_eval as YY
s=sys.argv[1]
M=[tuple(map(int,t.split(','))) for t in s.strip('()').split(')(')]
C=Ctx(M);x=len(M)-1;T=Ctx(M[:x])
print(bad2(C,T)[1])
k=C.upg(x-1);V=C.vOpt1(x-1);print('k',k,'P1',C.e.par(1,x-1))
ok,n,bad=upgabs_all(V,C.v(k))
for W,q in bad:
  print('W',YY.tstr(W));print('q',YY.tstr(q))
  # c=W witnesses
  from huac_structure_trio_codex import lvls
  for u in sorted(lvls(q),key=lambda t:len(str(t))):
    g=tmax(comps(u,q));K=tmax(comps(u,W)+[()])
    if lt(K,g):print(' fails at c=W, u=',YY.tstr(u))
