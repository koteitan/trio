"""Measure the StepDom sufficient conditions on the canonical deep witness
(j = last bump child of k, c = first child of j, a = chain element of m with e1 a = e1 c):
 (i)  every upgrade target t of a chain column y (a < y <= m on the chain) has no bump child
 (ii) v(a) has a level-0 component >= 1 (needed only if some U-step exists)
Also: canonical witness validity, StepDom itself, and structural data for the existence proof."""
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
def ms(C):return ''.join('(%d,%d,%d)'%t for t in C.M)
def run(batch):
 cnt=collections.Counter();ex={}
 def note(tag,C,d):
  cnt[tag]+=1
  s=ms(C)
  if tag not in ex or len(s)<len(ex[tag]['M']):
   d=dict(d);d['M']=s;ex[tag]=d
 for mm in batch:
  C=Ctx([tuple(t) for t in mm])
  if not C.ok:cnt['eval_FAIL']+=1;continue
  for n in range(len(C.M)):
   k=C.upg(n)
   if k is None or k>=n:continue
   m=C.e.par(1,k);V=C.v(m);W=C.bumpW(k)
   if not any(g!=Z for q in summ(V) if lt(q,W) for g in cs(Z,q)):continue
   if W[0]==Z:continue
   cnt['danger_pos']+=1
   js=[j for j in C.ch(k) if C.M[j]==C.e.bump(k)]
   ret=bool(js) and bool(C.ch(js[-1])) and C.ch(js[-1])[-1]<n and C.M[C.ch(js[-1])[-1]][1]==C.M[m][1] and C.M[C.ch(js[-1])[-1]][2]==0
   if ret:cnt['return']+=1
   if not js:note('NO_BUMP_CHILD',C,{'n':n,'k':k});continue
   j=js[-1];ch=chain(C,m);kids=C.ch(j)
   if not kids:note('NO_GRANDCHILD',C,{'n':n,'k':k,'j':j});continue
   c=kids[0];G=sumN([C.o(d) for d in kids])
   lv={C.M[a][1]:i for i,a in enumerate(ch)}
   info={'n':n,'k':k,'m':m,'j':j,'c':c}
   good=c<n and C.o(c) in summ(G) and C.M[c][2]==0 and C.M[c][1] in lv
   if not good:
    note('canon_bad_ret%s'%ret,C,dict(info,c_lt_n=c<n,surv=C.o(c) in summ(G),e2=C.M[c][2],e1=C.M[c][1]));continue
   i=lv[C.M[c][1]];a=ch[i];info['a']=a;info['i']=i
   cnt['canon_ok']+=1;cnt['canon_i%d'%min(i,3)]+=1
   cnt['j_lt_n_%s'%(j<n)]+=1
   cnt['c_e1_le_n_%s'%(C.M[c][1]<=C.M[n][1])]+=1
   isub=True;anyU=False;sd=True
   for y in ch[:i]:
    t=C.upg(y)
    if t is None:continue
    anyU=True
    if any(C.M[d]==C.e.bump(t) for d in C.ch(t)):isub=False
    if not dom(Y.last(C.v(t)),C.v(a)):sd=False
   ii=any(g!=Z for g in cs(Z,C.v(a)))
   cnt['anyU_%s'%anyU]+=1
   if anyU:
    if not isub:note('I_FAIL',C,info)
    if not ii:note('II_FAIL',C,info)
   if not sd:note('STEPDOM_FAIL',C,info)
   if anyU and isub and ii:cnt['suff_ok_U']+=1
   if (not anyU) or (isub and ii):cnt['suff_ok']+=1
   else:note('SUFF_FAIL_stepdom%s'%sd,C,info)
   cnt['ii_any_%s'%ii]+=1
 return dict(cnt),ex
if __name__=='__main__':
 src=sys.argv[1];tag=sys.argv[2]
 mats=pickle.load(open(src,'rb'))
 if isinstance(mats,dict):mats=mats['seeds']+mats['ext']
 cnt=collections.Counter();ex={};t0=time.time();done=0
 with Pool(4) as pool:
  for cc,ee in pool.imap_unordered(run,(mats[i:i+200] for i in range(0,len(mats),200)),chunksize=1):
   cnt.update(cc);done+=200
   for t,e in ee.items():
    if t not in ex or len(e['M'])<len(ex[t]['M']):ex[t]=e
   if done%200000==0:print(done,round(time.time()-t0),dict(cnt),flush=True)
 json.dump({'src':src,'total':len(mats),'sec':time.time()-t0,'counts':dict(cnt),'ex':ex},open('/home/koteitan/proofs/trio/tmp/wf/WfHUAC2/ij_%s.json'%tag,'w'),indent=1)
 print('final',dict(cnt),flush=True)
