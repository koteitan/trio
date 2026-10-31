"""Graft family around the 36-column SrcC3Res counterexample (WfReM, 2026-10-31).
Seeds: cex36 M, its 35-column frame, graftBb2St / b2grow1 / b2grow2 matrices whose t=2 frame
(x last, r = P2 x) has a column c != r with v(c) = v(r); plus their prefixes ending at such a frame.
Grafts (generation 1):
 (a) child of c with v(c) = v(r): insert (e0 c + 1, a, b) as first child (right after c) or last child
     (after the subtree of c), a in 0..e1 c + 2, b in {0,1};
 (b) for M and the frame: the same insertion under every column c (any v), and graft4-style one-column
     mutations (+-1 per entry, delete, duplicate, append).
Generation 2: (a) again on a sample of generation 1 that still has an eq column.
Keep bms-standard (bms -s = 1) and < SRO. Output graftM36.pkl (list of lists of tuples)."""
import sys,pickle,random,subprocess,itertools,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from multiprocessing import Pool
from huac_structure_trio_codex import Ctx
BMS='/home/koteitan/proofs/trio/bms'
SETD='/home/koteitan/proofs/trio/tmp/ytosk-handoff/sets/'
SRO=((0,0,0),(1,1,1),(2,1,1),(3,1,0),(2,0,0))
M36=[(0,0,0),(1,1,1),(2,1,1),(3,1,0),(1,1,1),(2,1,1),(3,1,0),(1,1,1),(2,1,0),(3,2,1),(4,2,1),(5,2,0),(3,2,1),(4,2,1),(5,1,0),(6,2,1),(7,2,1),(8,2,0),(6,2,1),(7,2,1),(8,1,0),(9,2,1),(10,2,1),(11,2,0),(9,2,1),(10,2,1),(11,1,0),(12,2,0),(12,0,0),(13,1,1),(14,1,1),(10,2,0),(11,3,1),(12,3,1),(13,1,0),(14,2,1)]
F35=M36[:27]+M36[28:]
def ms(M):return ''.join('(%d,%d,%d)'%tuple(c) for c in M)
def std(M):return subprocess.run([BMS,'-s',ms(M)],capture_output=True,text=True).stdout.strip()=='1'
def eqcols(M):
 """columns c != r with v(c) = v(r), r = P2 of the last column (None if no t=2 frame)."""
 try:C=Ctx(list(M))
 except Exception:return None
 if not C.ok:return None
 x=len(M)-1;r=C.e.par(2,x)
 if r is None:return None
 vr=C.v(r);return [c for c in range(x) if c!=r and C.v(c)==vr]
def subend(M,c):
 e=c+1
 while e<len(M) and M[e][0]>M[c][0]:e+=1
 return e
def inserts(M,cs):
 for c in cs:
  for a in range(0,M[c][1]+3):
   for b in (0,1):
    col=(M[c][0]+1,a,b)
    for pos in sorted({c+1,subend(M,c)}):
     if pos>=len(M):continue   # keep the last column x the last
     yield M[:pos]+[col]+M[pos:]
def muts(M):
 L=len(M)
 for i in range(1,L):
  for d in itertools.product((-1,0,1),repeat=3):
   if d==(0,0,0):continue
   col=tuple(M[i][j]+d[j] for j in range(3))
   if min(col)<0 or col[2]>1:continue
   yield M[:i]+[col]+M[i+1:]
  yield M[:i]+M[i+1:]
  yield M[:i]+[M[i]]+M[i:]
 for a in range(0,M[-1][0]+2):
  for b in range(0,4):
   for c in (0,1):yield M+[(a,b,c)]
def keep(N):return len(N)>=4 and tuple(N)<SRO and std(N)
def gen_eq(M):
 M=[tuple(c) for c in M];cs=eqcols(M)
 if not cs:return []
 return [tuple(N) for N in inserts(M,cs) if keep(N)]
def gen_all(M):
 M=[tuple(c) for c in M];out=[]
 for N in itertools.chain(inserts(M,range(len(M)-1)),muts(M)):
  if keep(N):out.append(tuple(N))
 return out
def seedscan(M):
 M=[tuple(c) for c in M];out=[]
 for j in range(4,len(M)+1):
  P=M[:j]
  if P[-1][2] and eqcols(P):out.append(tuple(P))
 return out
if __name__=='__main__':
 W='/home/koteitan/proofs/trio/tmp/wf/WfReM/'
 seeds=set()
 with Pool(4) as pool:
  for nm in ('graftBb2St','b2grow1','b2grow2'):
   mats=pickle.load(open(SETD+nm+'.pkl','rb'))
   if len(mats)>4000:random.seed(5);mats=random.sample(list(mats),4000)
   n0=len(seeds)
   for o in pool.imap_unordered(seedscan,mats,chunksize=20):seeds.update(o)
   print(nm,len(mats),'new eq seeds',len(seeds)-n0,flush=True)
  seeds=sorted(seeds);random.seed(7)
  if len(seeds)>1500:seeds=random.sample(seeds,1500)
  g1=set()
  for o in pool.imap_unordered(gen_all,[M36,F35]):g1.update(o)
  print('M36/F35 all-column grafts+muts',len(g1),flush=True)
  for o in pool.imap_unordered(gen_eq,seeds+[tuple(M36),tuple(F35)],chunksize=4):g1.update(o)
  print('gen1',len(g1),flush=True)
  s2=[N for N in sorted(g1) if eqcols(N)];random.seed(9)
  s2=random.sample(s2,min(1500,len(s2)))
  g2=set()
  for o in pool.imap_unordered(gen_eq,s2,chunksize=4):g2.update(o)
  allN=sorted(g1|g2|{tuple(M36)})
 print('gen2 new',len(g2-g1),'total',len(allN),flush=True)
 pickle.dump([list(N) for N in allN],open(W+'graftM36.pkl','wb'))
