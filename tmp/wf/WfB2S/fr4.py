# bump-parent frames, all positions: i = 1 and m upgrades to t: compare W = bumpW(k) and last v(t)
import sys,pickle,collections,json
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from multiprocessing import Pool
from stepfacts3_core_trio_codex import *
import huac_structure_trio_codex as H
def s(M):return ''.join('(%d,%d,%d)'%t for t in M)
def run(batch):
 cnt=collections.Counter();ex={}
 for mm in batch:
  M=[tuple(c) for c in mm]
  if len(M)<3 or tuple(M)>=SRO:continue
  C=Ctx(M)
  if not C.ok:continue
  for n in range(len(M)):
   k=C.upg(n)
   if k is None or k>=n:continue
   p=C.e.par(0,n);g=C.e.par(0,p) if p is not None else None
   if g is None or M[p]!=C.e.bump(g):continue
   m=C.e.par(0,k)
   W=C.bumpW(k)
   if W[0]==Z: continue
   js=[j for j in C.ch(k) if M[j]==C.e.bump(k)]
   if not js or not C.ch(js[-1]): cnt['NOCANON']+=1; continue
   c=C.ch(js[-1])[0]
   ch=chain(C,m)
   aa=[i for i,a in enumerate(ch) if M[a][1]==M[c][1]]
   i=aa[0]
   cnt['i%d'%min(i,3)]+=1
   if i>=2: ex.setdefault('i2',s(M)+' n=%d k=%d'%(n,k))
   if i!=1:continue
   t=C.upg(m)
   if t is None: continue
   L=Y.last(C.v(t))
   rel='eq' if L==W else ('Wlt' if lt(W,L) else 'Wgt')
   cnt['i1mU.'+rel+'.t%s'%('lt' if t<m else 'next')]+=1
   if rel=='Wgt': ex.setdefault('Wgt',s(M)+' n=%d k=%d m=%d t=%d'%(n,k,m,t))
 return cnt,ex
def load(src):
 p=src if src.startswith('/') else '/home/koteitan/proofs/trio/tmp/ytosk-handoff/sets/%s.pkl'%src
 mats=pickle.load(open(p,'rb'))
 if isinstance(mats,dict):mats=mats['seeds']+mats['ext'] if 'seeds' in mats else list(mats.values())
 return mats
if __name__=='__main__':
 with Pool(int(sys.argv[1])) as pool:
  for src in sys.argv[2:]:
   mats=load(src)
   cnt=collections.Counter();ex={}
   for c,e in pool.imap_unordered(run,(mats[i:i+200] for i in range(0,len(mats),200)),chunksize=1):
    cnt.update(c)
    for a,b in e.items(): ex.setdefault(a,b)
   print(json.dumps({'set':src.split('/')[-1],'n':len(mats),'cnt':dict(sorted(cnt.items())),'ex':ex}),flush=True)
