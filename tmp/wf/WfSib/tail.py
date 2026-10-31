# value form H7WTail on the hunt matrices: Dom(v(P1(x-1)), v(c)) for each u-level (H.dom)
import sys,pickle
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfSib')
from stepfacts3_core_trio_codex import *
from hunt import frame,s
for N in pickle.load(open('hunt_found.pkl','rb')):
  N=[tuple(c) for c in N];C=Ctx(N);f=frame(N);c=f[1];n=f[2];k=f[3]
  print(H.dom(C.vOpt1(n),C.v(c)), H.dom(C.vOpt1(n),C.v(n)), len(N))
