"""Lift B-frame matrices to larger row-1 values: seed S = M[:n+2] (B frame at n, nonzero case), append every column x
with S+x standard, expand by 2 and 3, keep all expansions (prefixes are scanned by fr6 all / bdist).
Gen 2: repeat on the B-frame prefixes of gen-1 with b >= 3."""
import sys,pickle,random,collections,json,subprocess
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from multiprocessing import Pool
from stepfacts3_core_trio_codex import Ctx,SRO
import os
BMIN=int(os.environ.get('BMIN','2'))
import trio
BMS='/home/koteitan/proofs/trio/bms'
def s(M):return ''.join('(%d,%d,%d)'%t for t in M)
def std(M):return subprocess.run([BMS,'-s',s(M)],capture_output=True,text=True).stdout.strip()=='1'
def bframes(M,bmin):
 C=Ctx(M);out=[]
 if not C.ok:return out
 for n in range(len(M)-1):
  k=C.upg(n)
  if k is None or k>=n:continue
  p=C.e.par(0,n);g=C.e.par(0,p) if p is not None else None
  if g is None or M[p]!=C.e.bump(g):continue
  if M[k][1]<bmin:continue
  out.append(tuple(M[:n+2]))
 return out
def seeds_of(M):
 M=[tuple(c) for c in M]
 if len(M)<3 or tuple(M)>=SRO:return []
 return bframes(M,BMIN)
def grow(S):
 S=list(S);out=[]
 last=S[-1]
 for a in range(1,last[0]+2):
  for b in range(0,last[1]+3):
   for z in (0,1):
    T=S+[(a,b,z)]
    if not std(T):continue
    for nn in (2,3):
     E=trio.expand(T,nn)
     if len(E)<=110:out.append(tuple(E))
 return out
if __name__=='__main__':
 out=sys.argv[1];srcs=sys.argv[3:];NS=int(sys.argv[2])
 seeds=set()
 with Pool(4) as pool:
  for f in srcs:
   mats=pickle.load(open(f,'rb'))
   if isinstance(mats,dict):mats=list(mats.values())
   random.seed(7);mats=random.sample(mats,min(len(mats),4000))
   for r in pool.imap_unordered(seeds_of,mats,chunksize=20):seeds.update(r)
 seeds=sorted(seeds);random.seed(9);seeds=random.sample(seeds,min(NS,len(seeds)))
 print('seeds',len(seeds),flush=True)
 G=set()
 with Pool(4) as pool:
  for r in pool.imap_unordered(grow,seeds,chunksize=1):G.update(r)
 G=sorted(G);pickle.dump([list(x) for x in G],open(out,'wb'));print('lift',len(G),flush=True)
