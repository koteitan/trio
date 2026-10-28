"""Graft the H10Big antecedent shape onto real roots.
For M in sets, every r with e2 r = 1, upg(r-1) = r, g = P0 r, r-1 != g, every prefix end j inside r's subtree
(j = r+1 .. end of subtree), every a in 1..e1 r:  N = M[:j] + [bump(r), (e0r+2, a, 0), (e0r+1, 0, 0)].
Optionally also put a copy of c = (e0r+2, a', 0) children inside p before x-1 (variant 'pkid').
Keep N if the structural antecedent (frame + U + K + Bad2 shape) holds; then bms -s and N < SRO.
Usage: nice -n 15 python3 gen_shape.py OUT.pkl set1 set2 ...
"""
import sys,json,pickle,time,collections,subprocess
from pathlib import Path
from multiprocessing import Pool
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import huac_structure_trio_codex as H
from huac_structure_trio_codex import Y
SRO=((0,0,0),(1,1,1),(2,1,1),(3,1,0),(2,0,0))

def anc(E,a,b):
 while b is not None:
  if a==b:return True
  b=E.par(0,b)
 return False

def antecedent(N):
 M=list(N)
 if len(M)<3 or M[-1][1] or not any(M[-1]):return None
 try:E=Y.Ev(M)
 except Exception:return None
 x=len(M)-1;r=E.par(0,x)
 if r is None or r==x-1:return None
 g=E.par(0,r)
 if g is None or r-1==g or M[r]==E.bump(g) or (r in E.upgs and E.topped(r)):return None
 if not Y.Ev(M[:-1]).topped(r):return None
 if E._upg[r-1]!=r or E._upg[x-1] is None:return None
 p=E.par(0,x-1);b=E.par(0,p) if p is not None else None
 if not(p is not None and b is not None and M[p]==E.bump(b) and anc(E,b,x)):return None
 return (r,g,M[g][1])

def gen(batch):
 out=set()
 for mm in batch:
  M=tuple(map(tuple,mm))
  if M>=SRO:continue
  try:E=Y.Ev(list(M))
  except Exception:continue
  n=len(M)
  for r in range(1,n):
   if M[r][2]!=1 or E._upg[r-1]!=r:continue
   g=E.par(0,r)
   if g is None or r-1==g:continue
   end=r+1
   while end<n and M[end][0]>M[r][0]:end+=1
   e0,e1,_=M[r]
   for j in range(r+1,end+1):
    for a in range(1,e1+1):
     tails=[((e0+1,e1,1),(e0+2,a,0),(e0+1,0,0))]
     for a2 in range(1,e1+1):tails.append(((e0+1,e1,1),(e0+2,a2,0),(e0+2,a,0),(e0+1,0,0)))
     for t in tails:
      N=M[:j]+t
      if N<SRO and len(N)<=160:out.add(N)
 res=[]
 for N in out:
  a=antecedent(N)
  if a is not None:res.append((N,a))
 return res

if __name__=='__main__':
 outp=Path(sys.argv[1]);start=time.time();cand={}
 with Pool(4) as pool:
  for nm in sys.argv[2:]:
   mats=pickle.load(open(H.SETD/(nm+'.pkl'),'rb'))
   for res in pool.imap_unordered(gen,(mats[i:i+200] for i in range(0,len(mats),200)),chunksize=1):
    for N,a in res:cand[N]=a
   print(nm,'structural antecedents so far',len(cand),collections.Counter(a[2] for a in cand.values()),round(time.time()-start),flush=True)
 std=[]
 for N in sorted(cand,key=lambda N:(len(N),N)):
  text=''.join('(%d,%d,%d)'%t for t in N)
  o=subprocess.run(['/home/koteitan/proofs/trio/bms','-s',text],text=True,capture_output=True,check=True).stdout.strip()
  if o=='1':std.append(N)
 print('standard',len(std),collections.Counter(cand[N][2] for N in std),round(time.time()-start),flush=True)
 pickle.dump(std,open(outp,'wb'))
