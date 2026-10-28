"""(1) frames n->k (anc) whose last bump child j is a leaf: lev W, danger.
(2) universal: for every bump child j (of any p) with children, the first child's o survives."""
import sys,json,pickle,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from multiprocessing import Pool
import huac_structure_trio_codex as H
from huac_structure_trio_codex import Ctx,Z,ONE,Y,lt,summ,cs,sumN
def run(batch):
 cnt=collections.Counter();ex={}
 for mm in batch:
  C=Ctx([tuple(t) for t in mm])
  if not C.ok:continue
  for p in range(len(C.M)):
   for j in C.ch(p):
    if C.M[j]!=C.e.bump(p):continue
    kids=C.ch(j)
    if not kids:continue
    G=sumN([C.o(d) for d in kids]);s=C.o(kids[0]) in summ(G)
    cnt['surv_%s'%s]+=1
    if not s:
     t=''.join('(%d,%d,%d)'%x for x in C.M)
     if 'surv' not in ex or len(t)<len(ex['surv'][0]):ex['surv']=(t,p,j)
  for n in range(len(C.M)):
   k=C.upg(n)
   if k is None or k>=n:continue
   js=[j for j in C.ch(k) if C.M[j]==C.e.bump(k)]
   if js and not C.ch(js[-1]):
    W=C.bumpW(k);m=C.e.par(0,k);V=C.v(m)
    dg=any(g!=Z for q in summ(V) if lt(q,W) for g in cs(Z,q))
    cnt['jleaf_levz_%s_danger_%s_nb%d'%(W[0]==Z,dg,len(js))]+=1
 return dict(cnt),ex
if __name__=='__main__':
 for nm in sys.argv[1:]:
  mats=pickle.load(open(H.SETD/(nm+'.pkl'),'rb'));cnt=collections.Counter();ex={}
  with Pool(4) as pool:
   for cc,ee in pool.imap_unordered(run,(mats[i:i+200] for i in range(0,len(mats),200))):
    cnt.update(cc);ex.update(ee)
  print(nm,dict(cnt),ex,flush=True)
