"""Counterexample hunt for H7WSib (t0 Bad2 lost-tail frame: col c = col(x-1) and upg c = upg(x-1)).
Seeds: H7WSib frames (structural F3) from graft families. Grafts concentrated in the r-subtree:
insert one column, insert two columns, replace c, duplicate c's subtree with row-1 / row-2 lifts.
Keep: F3 frame with c != x-1 structurally (col or upg differs) and row 1 of m != 0; then bms-standard; then Bad2."""
import sys,json,pickle,collections,subprocess,itertools,random
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from multiprocessing import Pool
import ytosk_eval2 as Y2
BMS='/home/koteitan/proofs/trio/bms'
SRO=((0,0,0),(1,1,1),(2,1,1),(3,1,0),(2,0,0))
def s(M):return ''.join('(%d,%d,%d)'%c for c in M)
def std(M):
 return subprocess.run([BMS,'-s',s(M)],capture_output=True,text=True).stdout.strip()=='1'
def frame(M):
 """returns (r,c,n,k,m) of the F3 frame or None"""
 if len(M)<4 or tuple(M)>=SRO:return None
 x=len(M)-1;n=x-1
 if M[x][1]!=0 or M[x]==(0,0,0):return None
 try:E=Y2.Ev2(M)
 except Exception:return None
 k=E._upg[n]
 if k is None or k>=n:return None
 r=E.par(0,x)
 if r is None or r==n or E.par(0,n)!=r:return None
 g=E.par(0,r)
 if g is None or M[r]!=E.bump(g) or M[g][1]==0 or M[g][2]==0:return None
 ch=[d for d in E.children[r] if d<x]
 if len(ch)<2 or ch[-1]!=n:return None
 c=ch[-2];m=E.par(1,n)
 return (r,c,n,k,m,E._upg[c],g)
def bad(M,f):
 r,c,n,k,m,uc,g=f
 return not(M[c]==M[n] and uc==k)
def muts(M,f):
 r,c,n,k,m,uc,g=f
 x=len(M)-1
 e0r=M[r][0];e1g=M[g][1]
 cols=[(a,b,z) for a in range(e0r+1,e0r+5) for b in range(0,e1g+2) for z in (0,1)]
 # one inserted column in (r, x-1]
 for i in range(r+1,x):
  for col in cols:yield M[:i]+[col]+M[i:]
 # replace one column in (r, x-1]
 for i in range(r+1,x):
  for col in cols:
   if col!=M[i]:yield M[:i]+[col]+M[i+1:]
 # duplicate c's subtree (c..n-1) with lifts
 B=M[c:n]
 for d1 in (0,1):
  for d2 in (0,1):
   B2=[(a,b+d1,min(1,z+d2)) for (a,b,z) in B]
   B3=[(B2[0][0],B2[0][1],B2[0][2])]+B[1:]
   for BB in (B2,B3):
    yield M[:c]+BB+M[c:]
    yield M[:n]+BB+M[n:]
 # two inserted columns (random sample)
 rnd=random.Random(len(M)*1000+c)
 for _ in range(400):
  i=rnd.randrange(r+1,x);j=rnd.randrange(i,x)
  a=rnd.choice(cols);b=rnd.choice(cols)
  N=M[:i]+[a]+M[i:j]+[b]+M[j:]
  yield N
def work(M):
 M=[tuple(c) for c in M]
 f0=frame(M)
 cnt=collections.Counter();out=[]
 if f0 is None:return cnt,out
 seen=set()
 for N in muts(M,f0):
  t=tuple(N)
  if t in seen:continue
  seen.add(t)
  f=frame(N)
  if f is None:continue
  cnt['F3']+=1
  if not bad(N,f):continue
  m=f[4]
  if m is None or N[m][1]==0:cnt['bad.m0']+=1;continue
  cnt['bad.m+']+=1
  if not std(N):continue
  cnt['bad.m+.std']+=1;out.append(N)
 return cnt,out
if __name__=='__main__':
 seeds=[]
 for f in sys.argv[1:]:
  mats=pickle.load(open(f,'rb'))
  if isinstance(mats,dict):mats=mats['seeds']+mats['ext'] if 'seeds' in mats else list(mats.values())
  for mm in mats:
   M=[tuple(c) for c in mm]
   if frame(M):seeds.append(M)
 random.seed(0);random.shuffle(seeds)
 import os;seeds=seeds[:int(os.environ.get("CAP","1000000000"))]
 print('seeds',len(seeds),flush=True)
 cnt=collections.Counter();found=[]
 with Pool(4) as pool:
  for c,o in pool.imap_unordered(work,seeds,chunksize=2):
   cnt.update(c)
   for N in o:
    found.append(N);print('STD-STRUCT-CEX',s(N),flush=True)
 pickle.dump(found,open('/home/koteitan/proofs/trio/tmp/wf/WfSib/hunt_found.pkl','wb'))
 print(json.dumps(dict(cnt)),flush=True)
