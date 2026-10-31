"""GenSmall: k (e1,e2!=0), P0 k = P1 k = m, k not topped, j bump child of k, c child of j:
SmallB(v(m)) c. Frame-wide (no Bad2/DropFail filter).  Usage: probe_g1.py [--upg] SET..."""
import sys,json,collections,pickle,time
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from multiprocessing import Pool
from huac_structure_trio_codex import Ctx,Y,lt,le,Z
UPG='--upg' in sys.argv
def mt(M):return ''.join('(%d,%d,%d)'%tuple(t) for t in M)
def smallB(C,V,c,dep=0):
 vc=C.v(c)
 if lt(vc,V):return True,dep
 if vc!=V:return False,dep
 md=dep
 for d in C.CL(c):
  ok,dd=smallB(C,V,d,dep+1)
  if not ok:return False,dd
  md=max(md,dd)
 return True,md
def run(batch):
 cnt=collections.Counter();ex=[]
 for mm in batch:
  M=[tuple(t) for t in mm]
  try:C=Ctx(M)
  except Exception:continue
  if not C.ok:continue
  E=C.e;n=len(M)
  ups=set(u for u in E._upg if u is not None)
  for k in range(n):
   if not C.e12(k):continue
   m=E.par(0,k)
   if m is None or E.par(1,k)!=m:continue
   if E.topped(k):continue
   if UPG and k not in ups:continue
   vm=C.v(m)
   for j in C.ch(k):
    if M[j]!=E.bump(k):continue
    for c in C.ch(j):
     cnt['n']+=1
     ok,d=smallB(C,vm,c)
     cnt['G1.'+str(ok)]+=1
     cnt['vc_le_vm.'+str(le(C.v(c),vm))]+=1
     if ok:cnt['depth.%d'%d]+=1
     # E: v(c)=v(m) -> counted children have e1 <= e1 c
     if C.v(c)==vm:
      cnt['eq']+=1
      cnt['E_cl_e1_le.'+str(all(M[d][1]<=M[c][1] for d in C.CL(c)))]+=1
      cnt['E_cl_e1_lt.'+str(all(M[d][1]<M[c][1] for d in C.CL(c)))]+=1
      cnt['e1c_eq_e1m.'+str(M[c][1]==M[m][1])]+=1
     if not ok and len(ex)<6:ex.append(dict(M=mt(M),m=m,k=k,j=j,c=c))
 return dict(cnt),ex
if __name__=='__main__':
 out={}
 for nm in [a for a in sys.argv[1:] if not a.startswith('--')]:
  t=time.time()
  mats=pickle.load(open('/home/koteitan/proofs/trio/tmp/ytosk-handoff/sets/%s.pkl'%nm,'rb'))
  cnt=collections.Counter();ex=[]
  with Pool(3) as pool:
   for c,b in pool.imap_unordered(run,(mats[i:i+300] for i in range(0,len(mats),300))):cnt.update(c);ex+=b
  out[nm]={'counts':dict(sorted(cnt.items())),'ex':ex[:4],'sec':round(time.time()-t,1)}
  print(nm,len(mats),json.dumps(out[nm]),flush=True)
