"""For every k with e2 k = 1 and P0 k = P1 k = m, j = last bump child of k with children, c = first child of j,
not all bump grandchildren row1 = 0: i = e1 m - e1 c. Classify by local features of k's later children."""
import sys,pickle,collections,json
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from multiprocessing import Pool
from stepfacts3_core_trio_codex import *
def s(M):return ''.join('(%d,%d,%d)'%t for t in M)
def run(batch):
 cnt=collections.Counter();ex={}
 for mm in batch:
  M=[tuple(c) for c in mm]
  if len(M)<3 or tuple(M)>=SRO:continue
  C=Ctx(M)
  if not C.ok:continue
  for k in range(len(M)):
   if M[k][2]!=1:continue
   m=C.e.par(0,k)
   if m is None or C.e.par(1,k)!=m:continue
   bj=[j for j in C.ch(k) if M[j]==C.e.bump(k)]
   if all(M[c][1]==0 for j in bj for c in C.ch(j)):continue
   js=[j for j in bj if C.ch(j)]
   c=C.ch(js[-1])[0]
   i=M[m][1]-M[c][1]
   # later non-bump children of k
   hs=[h for h in C.ch(k) if h>js[-1] and M[h]!=C.e.bump(k)]
   # does some n in subtree of k (after j) upgrade to k with bump parent
   ty=set();up=[]
   for n in range(k+1,len(M)-1):
    if C.upg(n)==k:
     up.append(n);p=C.e.par(0,n);g=C.e.par(0,p) if p is not None else None
     if p==k:ty.add('K')
     elif g is not None and M[p]==C.e.bump(g):ty.add('B')
     elif M[p][2]==1:ty.add('E')
     else:ty.add('O')
   hh=[h for h in C.ch(k) if M[h]==(M[k][0]+1,M[k][1],0)]
   # bump pair inside subtree of some hh with e1 > b
   def sub(h):
    out=[];q=h+1
    while q<len(M) and M[q][0]>M[h][0]: out.append(q);q+=1
    return out
   bp=any(M[q][2]==1 and C.e.par(0,q) is not None and M[q]==C.e.bump(C.e.par(0,q)) and M[q][1]>M[k][1] and all(M[w][1]>=M[k][1] for w in range(h,q+1) if w in sub(h) or w==h) for h in hh for q in sub(h))
   key='i%s %s h%d bp%d'%(min(i,3),''.join(sorted(ty)),len(hh)>0,bp)
   cnt[key]+=1
   if i>=2 and up and len(ex)<6: ex.setdefault(key,s(M)+' k=%d m=%d c=%d up=%s'%(k,m,c,up))
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
   print(json.dumps({'set':src.split('/')[-1],'cnt':dict(sorted(cnt.items())),'ex':ex}),flush=True)
