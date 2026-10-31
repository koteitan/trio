"""Grafts for B2LevS / B2UpgV. Seeds: matrices with an S.i1 frame (e1 c + 1 = e1 m, bump parent) at some position,
cut at n+2 (so the frame is at x-1), from cbadext, graft2, graft3, graft_b2, graft_sib; plus 60 random S.i0 seeds.
One column +-1 / delete / duplicate / append a column, bms-standard. Then fr6 (all positions)."""
import sys,json,pickle,collections,subprocess,itertools,random
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfB2S')
from multiprocessing import Pool
from stepfacts3_core_trio_codex import *
import fr6
BMS='/home/koteitan/proofs/trio/bms'
def std(M):
 s=''.join('(%d,%d,%d)'%c for c in M)
 return subprocess.run([BMS,'-s',s],capture_output=True,text=True).stdout.strip()=='1'
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
 last=M[-1]
 for a in range(0,last[0]+2):
  for b in range(0,4):
   for c in (0,1):
    yield M+[(a,b,c)]
def gen(M):
 out=[]
 for N in muts(list(M)):
  if len(N)>=4 and tuple(N)<SRO and std(N):out.append(tuple(N))
 return out
def frames(M):
 C=Ctx(M)
 if not C.ok:return []
 r=[]
 for n in range(len(M)):
  k=C.upg(n)
  if k is None or k>=n:continue
  p=C.e.par(0,n);g=C.e.par(0,p) if p is not None else None
  if g is None or M[p]!=C.e.bump(g):continue
  m=C.e.par(0,k);bj=[j for j in C.ch(k) if M[j]==C.e.bump(k)]
  js=[j for j in bj if C.ch(j)]
  if not js:continue
  c=C.ch(js[-1])[0]
  r.append((n,M[c][1]+1==M[m][1] and M[c][1]!=0))
 return r
def seedscan(M):
 M=[tuple(c) for c in M]
 if len(M)<3 or tuple(M)>=SRO:return [],[]
 a=[];b=[]
 for n,i1 in frames(M):
  (a if i1 else b).append(tuple(M[:n+2]))
 return a,b
if __name__=='__main__':
 W='/home/koteitan/proofs/trio/tmp/wf'
 files=['/home/koteitan/proofs/trio/tmp/ytosk-handoff/sets/cbadext.pkl',W+'/WfH7W2/graft2.pkl',W+'/WfH7W2/graft3.pkl',W+'/WfH7W/graft_b2.pkl',W+'/WfH7W/graft_sib.pkl']
 A=set();B=set()
 with Pool(3) as pool:
  for f in files:
   mats=pickle.load(open(f,'rb'))
   for a,b in pool.imap_unordered(seedscan,mats,chunksize=20):A.update(a);B.update(b)
 random.seed(11)
 A=sorted(A);B=sorted(B)
 sd=random.sample(A,min(200,len(A)))+random.sample(B,min(60,len(B)))
 print('seeds i1',len(A),'i0',len(B),'used',len(sd),flush=True)
 allN=set()
 with Pool(3) as pool:
  for o in pool.imap_unordered(gen,sd,chunksize=2):allN.update(o)
 allN=sorted(allN)
 pickle.dump([list(N) for N in allN],open(W+'/WfB2S/graft4.pkl','wb'))
 print('grafts',len(allN),flush=True)
