# Structural B2Step frames at every position n (upg n = k < n, P0 n a bump child): level index i, U-steps, StepDom,
# and at n = x-1: Bad2 / UpgAbsX
import sys,pickle,collections,json
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from multiprocessing import Pool
from stepfacts3_core_trio_codex import *
from bad2_exact_trio_codex import bad2
import huac_structure_trio_codex as H
def s(M):return ''.join('(%d,%d,%d)'%t for t in M)
ALL=False
def run(batch):
 cnt=collections.Counter();ex={}
 for mm in batch:
  M=[tuple(c) for c in mm]
  if len(M)<3 or tuple(M)>=SRO:continue
  x=len(M)-1
  C=Ctx(M)
  if not C.ok:continue
  T=None
  for n in (range(len(M)) if ALL else [x-1]):
   k=C.upg(n)
   if k is None or k>=n:continue
   p=C.e.par(0,n);g=C.e.par(0,p) if p is not None else None
   bp=not(g is None or M[p]!=C.e.bump(g))
   m=C.e.par(0,k)
   if C.bumpW(k)[0]==Z: cnt['levzero']+=1; continue
   js=[j for j in C.ch(k) if M[j]==C.e.bump(k) and C.ch(j)]
   if not js: cnt['NOCANON.bp%s'%bp]+=1; ex.setdefault('NOCANON.bp%s'%bp,s(M)+' n=%d k=%d'%(n,k)); continue
   c=C.ch(js[-1])[0]
   ch=chain(C,m)
   aa=[i for i,a in enumerate(ch) if M[a][1]==M[c][1]]
   if not aa: cnt['NOLEVEL.bp%s'%bp]+=1; ex.setdefault('NOLEVEL',s(M)+' n=%d k=%d'%(n,k)); continue
   i=aa[0];a=ch[i]
   us=[(y,C.upg(y)) for y in ch[:i] if C.upg(y) is not None]
   sd=all(H.dom(Y.last(C.v(t)),C.v(a)) for y,t in us)
   b='-'
   if n==x-1:
    if T is None: T=Ctx(M[:x])
    if T.ok:
     bb,info=bad2(C,T); b=('B2' if bb else 'nb')+('ua' if info.get('upgabs') else 'nua')
   ab=lt(Y.last(C.v(m)),C.bumpW(k)) if C.v(m)!=Z else False
   key='bp%s.ab%s.%s.i%d.U%d.mU%s.sd%s'%(bp,ab,b,min(i,3),min(len(us),3),C.upg(m) is not None,sd)
   cnt[key]+=1
   if key not in ex: ex[key]=s(M)+' n=%d k=%d m=%d c=%d a=%d us=%s'%(n,k,m,c,a,us)
 return cnt,ex
def load(src):
 p=src if src.startswith('/') else '/home/koteitan/proofs/trio/tmp/ytosk-handoff/sets/%s.pkl'%src
 mats=pickle.load(open(p,'rb'))
 if isinstance(mats,dict):mats=mats['seeds']+mats['ext'] if 'seeds' in mats else list(mats.values())
 return mats
if __name__=='__main__':
 if sys.argv[1]=='all': ALL=True; sys.argv.pop(1)
 with Pool(int(sys.argv.pop(1))) as pool:
  for src in sys.argv[1:]:
   mats=load(src)
   cnt=collections.Counter();ex={}
   for c,e in pool.imap_unordered(run,(mats[i:i+200] for i in range(0,len(mats),200)),chunksize=1):
    cnt.update(c)
    for a,b in e.items(): ex.setdefault(a,b)
   print(json.dumps({'set':src.split('/')[-1],'n':len(mats),'cnt':dict(sorted(cnt.items())),'ex':ex}),flush=True)
