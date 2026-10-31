"""B frames (n with bump parent p of g, upg n = k < n), nonzero case: features."""
import sys,pickle,collections,json
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from multiprocessing import Pool
from stepfacts3_core_trio_codex import *
def s(M):return ''.join('(%d,%d,%d)'%t for t in M)
def anc(C,a,b):
 while b is not None and b>a: b=C.e.par(0,b)
 return b==a
def run(batch):
 cnt=collections.Counter();ex={}
 for mm in batch:
  M=[tuple(c) for c in mm]
  if len(M)<3 or tuple(M)>=SRO:continue
  C=Ctx(M)
  if not C.ok:continue
  for n in range(len(M)-1):
   k=C.upg(n)
   if k is None or k>=n:continue
   p=C.e.par(0,n);g=C.e.par(0,p) if p is not None else None
   if g is None or M[p]!=C.e.bump(g):continue
   m=C.e.par(0,k);b=M[k][1]
   bj=[j for j in C.ch(k) if M[j]==C.e.bump(k)]
   if all(M[c][1]==0 for j in bj for c in C.ch(j)):continue
   js=[j for j in bj if C.ch(j)];j=js[-1]
   c=C.ch(j)[0];i=M[m][1]-M[c][1]
   # P1 of g, p
   P1g=C.e.par(1,g);
   f=('i%d'%i,'g1-b=%d'%(M[g][1]-b),'P1g=k' if P1g==k else ('P1g=m' if P1g==m else ('P1g>k' if P1g is not None and P1g>k else 'P1g<m')), 'upg(g)=%s'%('k' if C.upg(g)==k else ('none' if C.upg(g) is None else 'other')))
   cnt[' '.join(f)]+=1
   if len(ex)<8: ex.setdefault(' '.join(f),s(M)+' n=%d k=%d m=%d j=%d c=%d g=%d'%(n,k,m,j,c,g))
 return cnt,ex
if __name__=='__main__':
 np=int(sys.argv[1])
 with Pool(np) as pool:
  for src in sys.argv[2:]:
   mats=pickle.load(open(src,'rb'))
   if isinstance(mats,dict):mats=list(mats.values())
   cnt=collections.Counter();ex={}
   for c,e in pool.imap_unordered(run,(mats[i:i+200] for i in range(0,len(mats),200)),chunksize=1):
    cnt.update(c)
    for a,b in e.items(): ex.setdefault(a,b)
   print(json.dumps({'set':src.split('/')[-1],'cnt':dict(sorted(cnt.items()))}),flush=True)
   for a,b in ex.items():print(a,'|',b)
