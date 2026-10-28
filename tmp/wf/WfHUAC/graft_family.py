"""Targeted family for HUACDeepShape: seeds = standard matrices with a dangerous
deep-return frame (i>=1), from graftBb2St, b2grow2, graftA (bms-checked).
Family = seeds + bms-standard one-column extensions + two rounds of
expansions n=0..4 with all prefixes (len<=160, below SRO).  Saved as pkl."""
import sys,json,pickle,collections,subprocess
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from multiprocessing import Pool
import huac_structure_trio_codex as H
from huac_structure_trio_codex import Ctx,Z,ONE,lt,summ,cs,sumN
from deep_exist import chain,supp
import trio
SRO=((0,0,0),(1,1,1),(2,1,1),(3,1,0),(2,0,0))
def deep(M):
 C=Ctx([tuple(t) for t in M])
 if not C.ok:return False
 for n in range(len(C.M)):
  k=C.upg(n)
  if k is None or k>=n:continue
  m=C.e.par(1,k);V=C.v(m);W=C.bumpW(k)
  if W[0]==Z:continue
  if not any(g!=Z for q in summ(V) if lt(q,W) for g in cs(Z,q)):continue
  js=[j for j in C.ch(k) if C.M[j]==C.e.bump(k)]
  if js and C.ch(js[-1]):
   c=C.ch(js[-1])[-1]
   if c<n and C.M[c][1]==C.M[m][1] and C.M[c][2]==0:continue
  return True
 return False
def scan(batch):return [tuple(map(tuple,M)) for M in batch if deep(M)]
def std(M):
 if M>=SRO:return False
 t=''.join('(%d,%d,%d)'%x for x in M)
 return subprocess.run(['/home/koteitan/proofs/trio/bms','-s',t],text=True,capture_output=True).stdout.strip()=='1'
if __name__=='__main__':
 seeds=set()
 with Pool(4) as pool:
  for nm in ['graftBb2St','b2grow2','graftA']:
   mats=pickle.load(open(H.SETD/(nm+'.pkl'),'rb'))
   for r in pool.imap(scan,(mats[i:i+50] for i in range(0,len(mats),50))):seeds.update(r)
   print(nm,len(seeds),flush=True)
  seeds=sorted(seeds)
  ok=pool.map(std,seeds);seeds=[M for M,o in zip(seeds,ok) if o];print('std seeds',len(seeds),flush=True)
  # one-column extensions
  cand=set()
  for M in seeds:
   mx0=max(t[0] for t in M);mx1=max(t[1] for t in M)
   for a in range(1,mx0+2):
    for b in range(0,mx1+2):
     for c in (0,1):
      if len(M)<160:cand.add(M+((a,b,c),))
  cand=sorted(cand-set(seeds));ok=pool.map(std,cand,chunksize=200)
  ext=[M for M,o in zip(cand,ok) if o];print('ext1 cand',len(cand),'std',len(ext),flush=True)
 pickle.dump({'seeds':seeds,'ext':ext},open('/home/koteitan/proofs/trio/tmp/wf/WfHUAC/deepfam_stage1.pkl','wb'))
 fam=set(seeds)|set(ext);front=set(fam)
 est=sum(len(trio.expand([list(x) for x in M],n)) for M in list(front)[:200] for n in range(5))
 print('estimate round1 prefixes ~',est*len(front)//200,flush=True)
 for depth in range(int(sys.argv[1]) if len(sys.argv)>1 else 1):
  new=set()
  for M in front:
   for n in range(5):
    N=tuple(map(tuple,trio.expand([list(x) for x in M],n)))
    if len(N)>160 or N>=SRO:continue
    for k in range(2,len(N)+1):new.add(N[:k])
  front=new-fam;fam|=new;print('round',depth+1,len(front),len(fam),flush=True)
 pickle.dump([list(M) for M in sorted(fam)],open('/home/koteitan/proofs/trio/tmp/wf/WfHUAC/deepfam.pkl','wb'))
 json.dump({'seeds':len(seeds),'ext1':len(ext),'family':len(fam)},open('/home/koteitan/proofs/trio/tmp/wf/WfHUAC/deepfam_gen.json','w'))
