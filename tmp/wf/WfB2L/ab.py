"""B2StepAb at x-1 on every prefix with an upgrade frame (fr3 classes); FAIL = Bad2 & absorption & StepDom false."""
import sys,pickle,collections,json
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfB2S')
from multiprocessing import Pool
from stepfacts3_core_trio_codex import Ctx,SRO
import fr3
fr3.ALL=False
def run(batch):
 cnt=collections.Counter();ex={}
 for mm in batch:
  M=[tuple(c) for c in mm]
  if tuple(M)>=SRO:continue
  C=Ctx(M)
  if not C.ok:continue
  for n in range(1,len(M)-1):
   k=C.upg(n)
   if k is None or k>=n:continue
   p=C.e.par(0,n);g=C.e.par(0,p) if p is not None else None
   if g is None or M[p]!=C.e.bump(g):continue
   c,e=fr3.run([M[:n+2]])
   for a,v in c.items():
    if 'B2' not in a:continue
    key=('FAIL ' if '.abTrue' in a and 'sdFalse' in a else '')+a
    cnt[key]+=v
    if key.startswith('FAIL'):ex.setdefault(key,e.get(a))
 return cnt,ex
if __name__=='__main__':
 cnt=collections.Counter();ex={}
 with Pool(4) as pool:
  for f in sys.argv[1:]:
   mats=pickle.load(open(f,'rb'))
   if isinstance(mats,dict):mats=list(mats.values())
   for c,e in pool.imap_unordered(run,(mats[i:i+50] for i in range(0,len(mats),50)),chunksize=1):
    cnt.update(c);ex.update(e)
   print(f,json.dumps(dict(sorted(cnt.items())),indent=0),flush=True);print(ex,flush=True);cnt=collections.Counter();ex={}
