# Bad2 B2Step frames: classify by Bad2 disjunct, level index i of a, upgrade of m, structure of c
import sys,pickle,collections,json
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from multiprocessing import Pool
from stepfacts3_core_trio_codex import *
from bad2_exact_trio_codex import bad2
import huac_structure_trio_codex as H
def s(M):return ''.join('(%d,%d,%d)'%t for t in M)
def run(batch):
 cnt=collections.Counter();ex={}
 for mm in batch:
  M=[tuple(c) for c in mm]
  if len(M)<3 or tuple(M)>=SRO:continue
  x=len(M)-1;n=x-1
  C=Ctx(M)
  if not C.ok:continue
  k=C.upg(n)
  if k is None or k>=n:continue
  T=Ctx(M[:x])
  if not T.ok:continue
  b,info=bad2(C,T)
  if not b:continue
  m=C.e.par(0,k)
  dis=('A' if info['first'] else '')+('B' if info['second'] else '')
  W=C.bumpW(k)
  if W[0]==Z: cnt[dis+'.levzero']+=1; continue
  js=[j for j in C.ch(k) if M[j]==C.e.bump(k)]
  c=C.ch(js[-1])[0]
  ch=chain(C,m)
  aa=[i for i,a in enumerate(ch) if M[a][1]==M[c][1]]
  i=aa[0];a=ch[i]
  um=C.upg(m)
  # position facts
  key='%s.i%d.mU%s.mk%s.c=%s'%(dis,min(i,3),um is not None,'eq' if m==C.e.par(1,n) else 'ne', 'n' if c==n else ('lt' if c<n else 'gt'))
  cnt[key]+=1
  if key not in ex: ex[key]=s(M)+' n=%d k=%d m=%d j=%d c=%d a=%d um=%s p=%s g=%s'%(n,k,m,js[-1],c,a,um,info['p'],info['g'])
 return cnt,ex
def load(src):
 p=src if src.startswith('/') else '/home/koteitan/proofs/trio/tmp/ytosk-handoff/sets/%s.pkl'%src
 mats=pickle.load(open(p,'rb'))
 if isinstance(mats,dict):mats=mats['seeds']+mats['ext'] if 'seeds' in mats else list(mats.values())
 return mats
if __name__=='__main__':
 with Pool(3) as pool:
  for src in sys.argv[1:]:
   mats=load(src)
   cnt=collections.Counter();ex={}
   for c,e in pool.imap_unordered(run,(mats[i:i+200] for i in range(0,len(mats),200)),chunksize=1):
    cnt.update(c)
    for a,b in e.items(): ex.setdefault(a,b)
   print(json.dumps({'set':src.split('/')[-1],'n':len(mats),'cnt':dict(sorted(cnt.items())),'ex':ex}),flush=True)
