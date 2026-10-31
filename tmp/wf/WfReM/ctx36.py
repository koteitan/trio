"""(2) StepCtxT2 / Inv3V2 fields on the 36-column M (and M[2], M[3]), every prefix.
Uses: codex residual_extension_local.run (Inv3V2 S/W fields via probe_inv2/frame7/trigs0/leafg, drop fields
via probe_dropres, HBumpExt, UpgAbsXW0, SibColU), t0_upg_direct_synthetic.check (structural SInv clauses,
inv_fields, PH3cG, FC3), bad2_exact (Bad2 per prefix), T2CBad."""
import sys,json,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/lead/probes')
import residual_extension_local_trio_codex as A
import t0_upg_direct_synthetic_trio_codex as S
from bad2_exact_trio_codex import bad2
from huac_structure_trio_codex import Ctx as HC
import trio
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfReM');from graft import M36,ms,std
OLD={'AbsD','AbsU','AbsUW','TPLo','TPLoW','AbsDW'}   # old global forms of inv_fields (not in Inv3V2; Inv3V2 has the seed forms)
def t2cbad(M):
 C=HC(M);x=len(M)-1;r=C.e.par(2,x);q=C.e.par(0,x)
 if r is None or q is None or q==r:return False
 cl=C.CL(r);return (not cl or cl[-1]!=q) and C.upg(x-1) is not None
def one(N,tag,rep):
 key=bytes(v for c in N for v in c)
 cnt,ex=A.run([key])
 fails={k:v for k,v in cnt.items() if k.endswith('.failures') or k.endswith('fail') or 'exception' in k}
 try:
  ck=S.check(N);st=ck['structural_failures'];nf=ck['new_frame_failures'];oi=ck['OLD_inv_probe_failures']
 except Exception as e:
  st={'check_exception':repr(e)};nf={};oi={}
 newinv={k:v for k,v in oi.items() if k not in OLD}
 try:b2=bad2(HC(N),HC(N[:-1]))[0] if len(N)>1 else False
 except Exception as e:b2='err'
 rep.append(dict(tag=tag,len=len(N),bad2=b2,t2cbad=t2cbad(N) if N[-1][2] else None,local_fail=fails,
  struct=st,frame=nf,inv_new=newinv,inv_old=sorted(oi)))
if __name__=='__main__':
 rep=[]
 fams={'M':M36}
 for n in (2,3):fams['M[%d]'%n]=[tuple(c) for c in trio.expand([list(c) for c in M36],n)]
 for nm,N in fams.items():
  print(nm,len(N),'std',std(N),flush=True)
  for j in range(2,len(N)+1):one(N[:j],'%s.take%d'%(nm,j),rep)
 bad=[r for r in rep if r['local_fail'] or r['struct'] or r['frame'] or r['inv_new']]
 tot=collections.Counter()
 for r in rep:
  for k in r['local_fail']:tot[k]+=1
  for k in r['inv_new']:tot['inv.'+k]+=1
  for k in r['frame']:tot['frame.'+k]+=1
  for k in r['struct']:tot['struct.'+k]+=1
 print('prefixes',len(rep),'with any failure',len(bad));print(json.dumps(dict(tot)))
 for r in rep:
  if r['tag'] in ('M.take36','M[2].take%d'%len(fams['M[2]']),'M[3].take%d'%len(fams['M[3]'])):print(json.dumps(r))
 for r in bad[:12]:print('FAIL',json.dumps(r))
 json.dump(rep,open('/home/koteitan/proofs/trio/tmp/wf/WfReM/ctx36.json','w'),indent=1)
