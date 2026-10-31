import sys,pickle,collections,json
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from multiprocessing import Pool
from stepfacts3_core_trio_codex import Ctx,SRO
def run(batch):
 cnt=collections.Counter()
 for mm in batch:
  M=[tuple(c) for c in mm]
  if len(M)<3 or tuple(M)>=SRO:continue
  C=Ctx(M)
  if not C.ok:continue
  for n in range(len(M)-1):
   k=C.upg(n)
   if k is None or k>=n:continue
   p=C.e.par(0,n);g=C.e.par(0,p) if p is not None else None
   if g is None or M[p]!=C.e.bump(g):continue
   m=C.e.par(0,k);bj=[j for j in C.ch(k) if M[j]==C.e.bump(k)]
   if all(M[c][1]==0 for j in bj for c in C.ch(j)):continue
   js=[j for j in bj if C.ch(j)];c=C.ch(js[-1])[0]
   cnt['b=%d e1c=%d'%(M[k][1],M[c][1])]+=1
 return cnt
if __name__=='__main__':
 cnt=collections.Counter()
 with Pool(3) as pool:
  for f in sys.argv[1:]:
   mats=pickle.load(open(f,'rb'))
   if isinstance(mats,dict):mats=list(mats.values())
   for c in pool.imap_unordered(run,(mats[i:i+200] for i in range(0,len(mats),200)),chunksize=1):cnt.update(c)
 print(json.dumps(dict(sorted(cnt.items()))))
