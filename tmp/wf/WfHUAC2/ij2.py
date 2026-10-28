"""Combined measurement on all ancestor upgrades n -> k (k < n), m = P0 k:
canonical witness j = LAST bump child of k, c = FIRST child of j, a = chain element of m
(row-1 chain) with e1 a = e1 c.  Structural categories (all frames, tagged by danger),
plus the StepDom sufficient conditions (i) no bump child at upgrade targets of chain
columns strictly above a, (ii) v(a) has a nonzero level-0 component."""
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
   dg=any(g!=Z for q in summ(V) if lt(q,W) for g in cs(Z,q)) and W[0]!=Z
   D='D' if dg else 'N'
   cnt[D+'frames']+=1
   info={'n':n,'k':k,'m':m}
   if C.e.par(0,k)!=m:note(D+'P0k_ne_m',C,info)
   js=[j for j in C.ch(k) if C.M[j]==C.e.bump(k)]
   if not js:cnt[D+'nobump']+=1;continue
   j=js[-1];info['j']=j
   if not j<n:note(D+'j_ge_n',C,info);continue
   kids=C.ch(j)
   if not kids:note(D+'j_leaf',C,info);continue
   c=kids[0];info['c']=c;ch=chain(C,m)
   e1c=C.M[c][1];e1m=C.M[m][1];e1k=C.M[k][1]
   lv={C.M[a][1]:i for i,a in enumerate(ch)}
   if e1c>e1k:cat='gt_k'
   elif e1c==e1k:cat='eq_k'
   elif e1c>e1m:cat='mid'
   elif e1c in lv:cat='chain'
   else:cat='between'
   if cat!='chain':note(D+'cat_'+cat,C,info);continue
   if C.M[c][2]!=0:note(D+'c_e2_1',C,info);continue
   if not c<n:note(D+'c_ge_n',C,info);continue
   G=sumN([C.o(d) for d in kids])
   if C.o(c) not in summ(G):note(D+'c_dies',C,info);continue
   i=lv[e1c];a=ch[i];info['a']=a;info['i']=i
   cnt[D+'canon_ok']+=1;cnt[D+'i%d'%min(i,3)]+=1
   isub=True;anyU=False;sd=True
   for y in ch[:i]:
    t=C.upg(y)
    if t is None:continue
    anyU=True
    if any(C.M[d]==C.e.bump(t) for d in C.ch(t)):isub=False
    if not dom(Y.last(C.v(t)),C.v(a)):sd=False
   ii=any(g!=Z for g in cs(Z,C.v(a)))
   if anyU:
    cnt[D+'anyU']+=1
    if not isub:note(D+'I_FAIL',C,info)
    if not ii:note(D+'II_FAIL',C,info)
   if not sd:note(D+'STEPDOM_FAIL',C,info)
   if anyU and not (isub and ii):note(D+'SUFF_FAIL_sd%s'%sd,C,info)
 return dict(cnt),ex
if __name__=='__main__':
 src=sys.argv[1];tag=sys.argv[2];np=int(sys.argv[3]) if len(sys.argv)>3 else 4
 mats=pickle.load(open(src,'rb'))
 if isinstance(mats,dict):mats=mats['seeds']+mats['ext']
 cnt=collections.Counter();ex={};t0=time.time();done=0
 with Pool(np) as pool:
  for cc,ee in pool.imap_unordered(run,(mats[i:i+200] for i in range(0,len(mats),200)),chunksize=1):
   cnt.update(cc);done+=200
   for t,e in ee.items():
    if t not in ex or len(e['M'])<len(ex[t]['M']):ex[t]=e
   if done%200000==0:print(done,round(time.time()-t0),dict(cnt),flush=True)
 json.dump({'src':src,'total':len(mats),'sec':time.time()-t0,'counts':dict(cnt),'ex':ex},open('/home/koteitan/proofs/trio/tmp/wf/WfHUAC2/ij2_%s.json'%tag,'w'),indent=1)
 print('final',dict(cnt),flush=True)
