"""graftM36x.pkl: expansions M[2], M[3] of a sample of graftM36 (all t=2 last columns, plus a sample of the rest),
with every prefix of M[n] longer than the bad root r (the copied region). Expansions of standard matrices are standard."""
import sys,pickle,random
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from multiprocessing import Pool
import trio
from huac_structure_trio_codex import Ctx
W='/home/koteitan/proofs/trio/tmp/wf/WfReM/'
SRO=((0,0,0),(1,1,1),(2,1,1),(3,1,0),(2,0,0))
def ex(M):
 M=[tuple(c) for c in M];out=set()
 if M[-1]==(0,0,0):return out
 try:
  E=Ctx(M).e;x=len(M)-1;r=min([p for p in (E.par(0,x),E.par(1,x),E.par(2,x)) if p is not None],default=0)
 except Exception:r=0
 for n in (2,3):
  N=[tuple(c) for c in trio.expand([list(c) for c in M],n)]
  for j in range(max(r+2,4),len(N)+1):
   P=tuple(N[:j])
   if P<SRO:out.add(P)
 return out
if __name__=='__main__':
 mats=pickle.load(open(W+'graftM36.pkl','rb'))
 t2=[M for M in mats if M[-1][2]];rest=[M for M in mats if not M[-1][2]]
 random.seed(13);sd=random.sample(t2,min(1500,len(t2)))+random.sample(rest,min(500,len(rest)))
 allN=set()
 with Pool(int(sys.argv[1]) if len(sys.argv)>1 else 3) as pool:
  for o in pool.imap_unordered(ex,sd,chunksize=20):allN.update(o)
 base=set(tuple(tuple(c) for c in M) for M in mats);allN-=base
 print('seeds',len(sd),'t2',len(t2),'expansion prefixes',len(allN),flush=True)
 pickle.dump([list(N) for N in sorted(allN)],open(W+'graftM36x.pkl','wb'))
