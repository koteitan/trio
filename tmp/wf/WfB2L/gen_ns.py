"""Non-standard grafts: standard M + 1..3 appended columns, all structural checks true, B2LevS false (fr6 all).
Then ArgDomCoreOn violations."""
import sys,pickle,random,collections,itertools
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfB2S');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfB2L')
from multiprocessing import Pool
import fr6,strc,adc
fr6.MODE='all'
def s(M):return ''.join('(%d,%d,%d)'%t for t in M)
def targeted(M):
 import stepfacts3_core_trio_codex as S
 C=S.Ctx(M);out=[]
 for k in range(len(M)):
  if M[k][2]!=1:continue
  m=C.e.par(0,k)
  if m is None or C.e.par(1,k)!=m:continue
  A=M[k][0]-1;b=M[k][1]
  bj=[j for j in C.ch(k) if M[j]==C.e.bump(k)]
  js=[j for j in bj if C.ch(j)]
  if not js:continue
  c=C.ch(js[-1])[0]
  if M[m][1]-M[c][1]<2 or M[c][1]==0:continue
  # cut after k's subtree, append h-structure
  end=k+1
  while end<len(M) and M[end][0]>M[k][0]:end+=1
  P=M[:end]
  for mid in ([],[(A+3,b,0)],[(A+3,b+1,0)],[(A+3,b+1,1)]):
   d=len(mid)
   for bb in (b+1,b+2,b+3):
    for xx in [(A+5+d,b,0),(A+5+d,b+1,1),(A+4+d,bb,1),(A+3,b,0)]:
     out.append(P+[(A+2,b,0)]+mid+[(A+3+d,bb,1),(A+4+d,bb,1),(A+5+d,b,0),xx])
 return out
def work(M):
 M=[tuple(c) for c in M];res=[]
 for N in targeted(M):
  try:
   if not all(strc.check(N).values()):continue
   c,e=fr6.run([N])
  except Exception:continue
  if c.get('S.FAIL'):res.append((s(N),adc.viol(N,first=True)))
 last=M[-1]
 cols=[(a,b,c) for a in range(1,last[0]+3) for b in range(0,8) for c in (0,1)]
 random.seed(len(M)*7+sum(map(sum,M)))
 for t in range(400):
  N=list(M)
  for _ in range(random.randint(1,4)):
   a0=N[-1][0];N.append((random.randint(max(1,a0-2),a0+1),random.randint(0,8),random.randint(0,1)))
  try:
   if not all(strc.check(N).values()):continue
   c,e=fr6.run([N])
  except Exception:continue
  if c.get('S.FAIL'):
   res.append((s(N),adc.viol(N,first=True)))
 return res
if __name__=='__main__':
 mats=pickle.load(open(sys.argv[1],'rb'));random.seed(3);sd=random.sample(mats,min(int(sys.argv[2]),len(mats)))
 cnt=collections.Counter();ex=[]
 with Pool(4) as pool:
  for r in pool.imap_unordered(work,sd,chunksize=2):
   for N,v in r:
    cnt['adc_viol' if v else 'adc_OK']+=1
    if not v and len(ex)<5:ex.append(N)
 print(dict(cnt));print('\n'.join(ex))
