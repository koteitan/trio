import sys,pickle
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfSib')
from stepfacts3_core_trio_codex import *
import ytosk_eval as YY
from hunt import frame
for N in pickle.load(open('hunt_found.pkl','rb'))[:3]:
  N=[tuple(c) for c in N];C=Ctx(N);r,c,n,k,m,uc,g=frame(N)
  print('v(m)',YY.tstr(C.v(m)),'v(c)',YY.tstr(C.v(c)),'v(n)',YY.tstr(C.v(n)),'v(k)',YY.tstr(C.v(k)),'P1 c',C.e.par(1,c),'m',m)
