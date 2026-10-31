import sys,pickle
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfSib')
from stepfacts3_core_trio_codex import *
from bad2_exact_trio_codex import bad2
from hunt import frame,s
F=pickle.load(open(sys.argv[1],'rb'))
for N in F:
  N=[tuple(c) for c in N];x=len(N)-1
  C=Ctx(N);T=Ctx(N[:x])
  if not(C.ok and T.ok):print('evalfail',s(N));continue
  b,info=bad2(C,T)
  f=frame(N)
  print(len(N),'Bad2' if b else 'noBad2', 'r,c,n,k,m,upg c,g=',f, 'colc',N[f[1]],'coln',N[f[2]],'e1m',N[f[4]][1])
  print('  ',s(N))
