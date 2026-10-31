import sys,pickle,collections,json,subprocess
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfB2S')
from multiprocessing import Pool
from stepfacts3_core_trio_codex import Ctx,SRO
import fr6,fr3
def cut(mm):
 M=[tuple(c) for c in mm];out=[]
 if tuple(M)>=SRO:return out
 C=Ctx(M)
 if not C.ok:return out
 for n in range(len(M)-1):
  fr6.MODE='x1'
  c,e=fr6.run([M[:n+2]])
  if c.get('S.FAIL'):out.append(tuple(M[:n+2]))
 return out
if __name__=='__main__':
 mats=pickle.load(open(sys.argv[1],'rb'));F=set()
 with Pool(4) as pool:
  for r in pool.imap_unordered(cut,mats,chunksize=20):F.update(r)
 F=sorted(F,key=len);pickle.dump([list(x) for x in F],open(sys.argv[2],'wb'));print('failing prefixes',len(F))
 fr3.ALL=False
 cnt=collections.Counter();ex={}
 for M in F:
  c,e=fr3.run([M]);cnt.update(c)
  for a,b in e.items():
   if a not in ex or len(b)<len(ex[a]):ex[a]=b
 print(json.dumps(dict(sorted(cnt.items())),indent=0))
 for a,b in ex.items():
  if 'B2' in a:print(a,'|',b)
