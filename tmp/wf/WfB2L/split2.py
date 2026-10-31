"""All positions n with bump parent and upg n = k < n. a = chain level of c (first child of last bump child of k with
children). Uin = upgrades at chain columns strictly between a and m. V' = (m upgrades to t, i >= 1) -> bumpW(k) <= last v(t)."""
import sys,pickle,collections,json
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from multiprocessing import Pool
from stepfacts3_core_trio_codex import *
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
   m=C.e.par(0,k)
   bj=[j for j in C.ch(k) if M[j]==C.e.bump(k)]
   if all(M[cc][1]==0 for j in bj for cc in C.ch(j)):cnt['zero']+=1;continue
   js=[j for j in bj if C.ch(j)]
   if not js:cnt['nocanon']+=1;continue
   c=C.ch(js[-1])[0];ch=chain(C,m)
   aa=[i for i,a in enumerate(ch) if M[a][1]==M[c][1]]
   if not aa:cnt['nolevel']+=1;continue
   i=aa[0]
   uin=[y for y in ch[1:i] if C.upg(y) is not None]
   cnt['i%d Uin%d'%(min(i,4),min(len(uin),1))]+=1
   if uin and len(ex)<3:ex['Uin%d'%len(ex)]=''.join('(%d,%d,%d)'%t for t in M)+' n=%d k=%d m=%d c=%d uin=%s'%(n,k,m,c,uin)
   if i>=1:
    t=C.upg(m)
    if t is not None:
     W=C.bumpW(k);Lt=Y.last(C.v(t));ok=(W==Lt or lt(W,Lt))
     cnt['Vp i%d %s'%(min(i,4),ok)]+=1
     if not ok and len(ex)<6:ex['V%d'%len(ex)]=''.join('(%d,%d,%d)'%t for t in M)+' n=%d k=%d m=%d c=%d t=%d'%(n,k,m,c,t)
 return cnt,ex
if __name__=='__main__':
 for f in sys.argv[1:]:
  mats=pickle.load(open(f,'rb'))
  if isinstance(mats,dict):mats=list(mats.values())
  cnt=collections.Counter();ex={}
  with Pool(4) as pool:
   for c,e in pool.imap_unordered(run,(mats[i:i+100] for i in range(0,len(mats),100)),chunksize=1):cnt.update(c);ex.update(e)
  print(f.split('/')[-1],json.dumps(dict(sorted(cnt.items()))),flush=True)
  for a,b in ex.items():print(' ',a,'|',b)
