"""Exact HUACDeepShape test (Lean WfHUACDeep, last bump child version):
danger & lev W != 0 -> ReturnWitness(last j, last c) or
DeepWitness: j = LAST bump child of k, c in children j with o c in summands G_j, c<n,
a on the row-1 chain of m with e1 c = e1 a, e2 c = 0, and StepDom:
for y on the chain strictly below a with upg y = t: dom(last v(t), v(a))."""
import sys,json,pickle,collections,time
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from multiprocessing import Pool
import huac_structure_trio_codex as H
from huac_structure_trio_codex import Ctx,Z,ONE,Y,lt,summ,cs,sumN,dom
def chain(C,m):
 r=[m]
 while True:
  p=C.e.par(1,r[-1])
  if p is None:return r
  r.append(p)
def supp(A,B):return set(summ(A))<=set(summ(B))|{ONE}
def run(batch):
 cnt=collections.Counter();ex={};nowit=[]
 for mm in batch:
  C=Ctx([tuple(t) for t in mm])
  if not C.ok:cnt['eval_FAIL']+=1;continue
  for n in range(len(C.M)):
   k=C.upg(n)
   if k is None or k>=n:continue
   cnt['anc_upg']+=1
   m=C.e.par(1,k);V=C.v(m);W=C.bumpW(k)
   if not any(g!=Z for q in summ(V) if lt(q,W) for g in cs(Z,q)):continue
   cnt['danger']+=1
   if W[0]==Z:cnt['zero']+=1;continue
   js=[j for j in C.ch(k) if C.M[j]==C.e.bump(k)]
   ret=bool(js) and bool(C.ch(js[-1])) and C.ch(js[-1])[-1]<n and C.M[C.ch(js[-1])[-1]][1]==C.M[m][1] and C.M[C.ch(js[-1])[-1]][2]==0
   if ret:cnt['return']+=1;continue
   ch=chain(C,m);found=None
   if js:
    j=js[-1];G=sumN([C.o(d) for d in C.ch(j)])
    for c in C.ch(j):
     if c>=n or C.o(c) not in summ(G) or C.M[c][2]!=0:continue
     for i,a in enumerate(ch):
      if C.M[c][1]!=C.M[a][1]:continue
      ok=True;sp=True
      for y in ch[:i]:
       t=C.upg(y)
       if t is None:continue
       L=Y.last(C.v(t))
       if not dom(L,C.v(a)):ok=False;break
       if not supp(L,C.v(a)):sp=False
      if ok:found=(c,i,a,sp);break
     if found:break
   if found:
    c,i,a,sp=found;cnt['deep_i%d'%min(i,3)]+=1;cnt['deep_support_%s'%sp]+=1
    if C.e.par(1,c)!=C.e.par(1,a) or C.upg(c)!=C.upg(a) or C.v(c)!=C.v(a):cnt['STRUCT_FAIL']+=1
   else:
    cnt['NOWIT']+=1;nowit.append(''.join('(%d,%d,%d)'%t for t in C.M)+' n=%d'%n)
 return dict(cnt),nowit
if __name__=='__main__':
 src=sys.argv[1];mats=pickle.load(open(src,'rb'));tag=sys.argv[2]
 cnt=collections.Counter();nowit=[];t0=time.time();done=0
 with Pool(4) as pool:
  for cc,nw in pool.imap_unordered(run,(mats[i:i+200] for i in range(0,len(mats),200)),chunksize=1):
   cnt.update(cc);nowit+=nw;done+=200
   if done%200000==0:print(done,round(time.time()-t0),dict(cnt),flush=True)
 nowit.sort(key=len)
 json.dump({'src':src,'total':len(mats),'sec':time.time()-t0,'counts':dict(cnt),'nowit':nowit[:200],'nowit_count':len(nowit)},open('/home/koteitan/proofs/trio/tmp/wf/WfHUAC/deep_exist2_%s.json'%tag,'w'),indent=1)
 print('final',dict(cnt),flush=True)
