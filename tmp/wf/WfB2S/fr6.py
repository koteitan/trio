# B2LevS (structural) and B2UpgV (value) with j = last bump child with children.
# mode x1: n = x-1 only; mode all: every n. Bump parent required.
import sys,pickle,collections,json
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from multiprocessing import Pool
from stepfacts3_core_trio_codex import *
def s(M):return ''.join('(%d,%d,%d)'%t for t in M)
MODE='x1'
def run(batch):
 cnt=collections.Counter();ex={}
 for mm in batch:
  M=[tuple(c) for c in mm]
  if len(M)<3 or tuple(M)>=SRO:continue
  C=Ctx(M)
  if not C.ok:continue
  x=len(M)-1
  for n in (range(len(M)) if MODE=='all' else [x-1]):
   k=C.upg(n)
   if k is None or k>=n:continue
   p=C.e.par(0,n);g=C.e.par(0,p) if p is not None else None
   if g is None or M[p]!=C.e.bump(g):continue
   m=C.e.par(0,k)
   bj=[j for j in C.ch(k) if M[j]==C.e.bump(k)]
   if all(M[c][1]==0 for j in bj for c in C.ch(j)): cnt['S.zero']+=1; continue
   js=[j for j in bj if C.ch(j)]
   c=C.ch(js[-1])[0]
   if not M[m][1]<=M[c][1]+1:
    cnt['S.FAIL']+=1; ex.setdefault('S.FAIL',s(M)+' n=%d k=%d m=%d c=%d'%(n,k,m,c)); continue
   if M[c][1]==M[m][1]: cnt['S.i0']+=1; continue
   cnt['S.i1']+=1
   t=C.upg(m)
   if t is None: cnt['i1.noU']+=1; continue
   W=C.bumpW(k);L=Y.last(C.v(t))
   ok=(W==L or lt(W,L))
   cnt['i1.U.V%s'%ok]+=1
   if not ok: ex.setdefault('V.FAIL',s(M)+' n=%d k=%d m=%d c=%d t=%d'%(n,k,m,c,t))
 return cnt,ex
def load(src):
 p=src if src.startswith('/') else '/home/koteitan/proofs/trio/tmp/ytosk-handoff/sets/%s.pkl'%src
 mats=pickle.load(open(p,'rb'))
 if isinstance(mats,dict):mats=mats['seeds']+mats['ext'] if 'seeds' in mats else list(mats.values())
 return mats
if __name__=='__main__':
 MODE=sys.argv[1];np=int(sys.argv[2])
 with Pool(np) as pool:
  for src in sys.argv[3:]:
   mats=load(src)
   cnt=collections.Counter();ex={}
   for c,e in pool.imap_unordered(run,(mats[i:i+200] for i in range(0,len(mats),200)),chunksize=1):
    cnt.update(c)
    for a,b in e.items(): ex.setdefault(a,b)
   print(json.dumps({'set':src.split('/')[-1],'mode':MODE,'n':len(mats),'cnt':dict(sorted(cnt.items())),'ex':ex}),flush=True)
