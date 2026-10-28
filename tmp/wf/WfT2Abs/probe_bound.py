"""T2AbsNBad: test the candidate decomposition  s < B(v(r)) <= W_N(i),  B(v)=psi_v(Omega_{v+1}).
Input: the distinct failed-drop cases of tmp/codex/t2_absn_growth_trio_codex.json (or a pickle of matrices)."""
import sys,json,collections,pickle
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import huac_structure_trio_codex as H
from huac_structure_trio_codex import Ctx,Y,lt,le,summ,Z
from lhd_exact import lhd
import trio
ONE=(Z,Z,Z);W2=(Z,(Z,Z,(Z,Z,Z)),Z)
def B(v):return (v,(Y.add(v,ONE),Z,Z),Z)
def fails(C,T,i):
 V=C.vOpt1(i);W=C.bumpW(i);WT=T.bumpW(i)
 return [q for q in summ(V) if not lt(q,W2) and not lt(q,WT) and lt(q,W) and not lhd(q,W)]
def check(M,cnt,bad):
 C=Ctx(M);T=Ctx(M[:-1]);x=len(M)-1
 if not C.ok or not T.ok:return
 r=C.e.par(2,x)
 if r is None:return
 for i in range(x):
  if not C.e12(i):continue
  qs=fails(C,T,i)
  if not qs:continue
  cnt['cases']+=1
  vrM=C.v(r);vrT=T.v(r)
  cnt['vrM_eq_vrT.'+str(vrM==vrT)]+=1
  for q in qs:
   cnt['q_head_sub_eq_vr.'+str(q[0]==vrM)]+=1
   cnt['q_head_sub_le_vr.'+str(le(q[0],vrM))]+=1
   cnt['q_lt_B(vrM).'+str(lt(q,B(vrM)))]+=1
   if not lt(q,B(vrM)):bad.append(('qB',M,i,r,Y.tstr(q),Y.tstr(vrM)))
  for n in (2,3,4):
   N=trio.expand(M,n);CN=Ctx(N)
   if not CN.ok:cnt['N_FAIL']+=1;continue
   vrN=CN.v(r);WN=CN.bumpW(i)
   cnt['vrN_eq_vrM.'+str(vrN==vrM)]+=1
   cnt['B(vrN)_le_WN.'+str(le(B(vrN),WN))]+=1
   cnt['B(vrM)_le_WN.'+str(le(B(vrM),WN))]+=1
   cnt['oNr_eq_WN.'+str(CN.o(r)==WN)]+=1
   cnt['B_le_oNr.'+str(le(B(vrN),CN.o(r)))]+=1
   if not le(B(vrM),WN):bad.append(('BW',M,i,r,n,Y.tstr(B(vrM)),Y.tstr(WN)))
if __name__=='__main__':
 d=json.load(open('/home/koteitan/proofs/trio/tmp/codex/t2_absn_growth_trio_codex.json'))
 mats={}
 for s in d['sets'].values():
  for e in s['cases'].values():mats[e['matrix_text']]=[tuple(t) for t in e['matrix']]
 cnt=collections.Counter();bad=[]
 for M in mats.values():check(M,cnt,bad)
 print(len(mats));print(json.dumps(dict(sorted(cnt.items())),indent=1));print(bad[:5])
