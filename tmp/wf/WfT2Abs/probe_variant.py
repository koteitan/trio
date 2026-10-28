"""Variant of the source bound without the take-side filter: at a failed-drop column i,
every summand q of v(P1 i) with q >= psi(2), q < W_M(i), not q <| W_M(i) satisfies q < B(v_M(r))."""
import sys,json,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfT2Abs')
from probe_sets import *
d=json.load(open('/home/koteitan/proofs/trio/tmp/codex/t2_absn_growth_trio_codex.json'))
mats={}
for s in d['sets'].values():
 for e in s['cases'].values():mats[e['matrix_text']]=([tuple(t) for t in e['matrix']],e['i'])
cnt=collections.Counter()
for M,i in mats.values():
 C=Ctx(M);T=Ctx(M[:-1]);x=len(M)-1;r=C.e.par(2,x)
 V=C.vOpt1(i);W=C.bumpW(i);WT=T.bumpW(i)
 allq=[q for q in summ(V) if not lt(q,W2) and lt(q,W) and not lhd(q,W)]
 cnt['n_allq.%d'%len(allq)]+=1
 cnt['allq_lt_B.'+str(all(lt(q,B(C.v(r))) for q in allq))]+=1
 cnt['allq_ge_WT.'+str(all(not lt(q,WT) for q in allq))]+=1
 cnt['nsummands.%d'%len(summ(V))]+=1
print(dict(cnt))
