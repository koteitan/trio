import sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from stepfacts3_core_trio_codex import *
from bad2_exact_trio_codex import bad2,lhd
import huac_structure_trio_codex as H
import re
def parse(s):return [tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',s)]
M=parse(sys.argv[1]);C=Ctx(M);T=Ctx(M[:-1]);x=len(M)-1;n=x-1
k=C.upg(n);m=C.e.par(0,k)
print('n',n,'k',k,'m',m,'P1n',C.e.par(1,n),'upg m',C.upg(m),'P1m',C.e.par(1,m))
for i in sorted(set([n,k,m,C.e.par(1,m)]+([C.upg(m)] if C.upg(m) is not None else []))):
  print(i,M[i],'v=',Y.tstr(C.v(i)))
W=C.bumpW(k);print('W',Y.tstr(W))
for q in H.summ(C.v(m)):print(' summand',Y.tstr(q),'<W',lt(q,W),'lhd',lhd(q,W))
print(bad2(C,T))
