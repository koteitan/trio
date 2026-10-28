"""Fresh family targeted at StepDom: seeds = bms-standard matrices having a dangerous
frame (lev W != 0) whose canonical witness has a U-step strictly above a.
Family = seeds + bms-standard one-column extensions + one round of expansions
n=0..4 with all prefixes (len <= 140, below SRO)."""
import sys,json,pickle,subprocess
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfHUAC2')
from multiprocessing import Pool
import huac_structure_trio_codex as H
from ij2 import run
import trio
SRO=((0,0,0),(1,1,1),(2,1,1),(3,1,0),(2,0,0))
def has_u(M):
 c,_=run([M]);return c.get('DanyU',0)>0
def scan(batch):return [tuple(map(tuple,M)) for M in batch if has_u(M)]
def std(M):
 if M>=SRO:return False
 t=''.join('(%d,%d,%d)'%x for x in M)
 return subprocess.run(['/home/koteitan/proofs/trio/bms','-s',t],text=True,capture_output=True).stdout.strip()=='1'
if __name__=='__main__':
 seeds=set()
 with Pool(4) as pool:
  for nm in sys.argv[1:]:
   mats=pickle.load(open(H.SETD/(nm+'.pkl'),'rb'))
   for r in pool.imap(scan,(mats[i:i+50] for i in range(0,len(mats),50))):seeds.update(r)
   print(nm,len(seeds),flush=True)
  seeds=sorted(seeds,key=lambda M:(len(M),M))[:800]
  ok=pool.map(std,seeds);seeds=[M for M,o in zip(seeds,ok) if o];print('std seeds',len(seeds),flush=True)
  cand=set()
  for M in seeds:
   mx0=max(t[0] for t in M);mx1=max(t[1] for t in M)
   for a in range(1,mx0+2):
    for b in range(0,mx1+2):
     for c in (0,1):
      if len(M)<140:cand.add(M+((a,b,c),))
  cand=sorted(cand-set(seeds));ok=pool.map(std,cand,chunksize=200)
  ext=[M for M,o in zip(cand,ok) if o];print('ext1 cand',len(cand),'std',len(ext),flush=True)
 fam=set(seeds)|set(ext);new=set()
 for M in list(fam):
  for n in range(5):
   N=tuple(map(tuple,trio.expand([list(x) for x in M],n)))
   if len(N)>140 or N>=SRO:continue
   for k in range(2,len(N)+1):new.add(N[:k])
 fam|=new;print('family',len(fam),flush=True)
 pickle.dump([list(M) for M in sorted(fam)],open('/home/koteitan/proofs/trio/tmp/wf/WfHUAC2/ufam.pkl','wb'))
 json.dump({'seeds':len(seeds),'ext1':len(ext),'family':len(fam)},open('/home/koteitan/proofs/trio/tmp/wf/WfHUAC2/ufam_gen.json','w'))
