"""At n = x-1 (every prefix): bump-parent frame, structural Bad2 shape
S2 := (x under g or e2 x != 0) or (P0 x = n and e1 x != 0). Count U (upgrades on the chain of m strictly above a)."""
import sys,pickle,collections,json
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from multiprocessing import Pool
from stepfacts3_core_trio_codex import Ctx,SRO,chain
from bad2_exact_trio_codex import bad2
def anc(C,a,b):
 while b is not None and b>a:b=C.e.par(0,b)
 return b==a
def run(batch):
 cnt=collections.Counter();ex={}
 for mm in batch:
  M0=[tuple(c) for c in mm]
  if tuple(M0)>=SRO:continue
  for L in range(3,len(M0)+1):
   M=M0[:L];x=L-1;n=x-1
   C=Ctx(M)
   if not C.ok:continue
   k=C.upg(n)
   if k is None or k>=n:continue
   p=C.e.par(0,n);g=C.e.par(0,p) if p is not None else None
   if g is None or M[p]!=C.e.bump(g):continue
   S2=(anc(C,g,x) or M[x][2]!=0) or (C.e.par(0,x)==n and M[x][1]!=0)
   m=C.e.par(0,k)
   if C.bumpW(k)[0]==((),) : pass
   js=[j for j in C.ch(k) if M[j]==C.e.bump(k) and C.ch(j)]
   if not js:cnt['nocanon S2%d'%S2]+=1;continue
   c=C.ch(js[-1])[0];ch=chain(C,m)
   aa=[i for i,a in enumerate(ch) if M[a][1]==M[c][1]]
   if not aa:cnt['nolevel S2%d'%S2]+=1;continue
   i=aa[0];us=[y for y in ch[:i] if C.upg(y) is not None]
   T=Ctx(M[:x]);b2=bad2(C,T)[0] if T.ok else None
   key='S2%d B2%s U%d'%(S2,b2,min(len(us),1))
   cnt[key]+=1
   if S2 and us and len(ex)<4:ex[key+str(len(ex))]=''.join('(%d,%d,%d)'%t for t in M)+' k=%d m=%d c=%d us=%s'%(k,m,c,us)
 return cnt,ex
if __name__=='__main__':
 for f in sys.argv[1:]:
  mats=pickle.load(open(f,'rb'))
  if isinstance(mats,dict):mats=list(mats.values())
  cnt=collections.Counter();ex={}
  with Pool(4) as pool:
   for c,e in pool.imap_unordered(run,(mats[i:i+30] for i in range(0,len(mats),30)),chunksize=1):cnt.update(c);ex.update(e)
  print(f,json.dumps(dict(sorted(cnt.items()))),flush=True)
  for a,b in ex.items():print(' ',a,'|',b)
