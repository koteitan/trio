"""Exact candidate DeepWitness on HUAC danger frames.
Choices: LAST bump child j of k (no later bump child), LAST child c of j.
Deep return: exists a on the P1 chain of m (a_0=m) with e1 c=e1 a, e2 c=0, e2 a=0.
Record also par1 c=par1 a, upg c=upg a, v c=v a, Support(v m, v a),
per-step U increments Support(last v(upg x), v a) for x on chain strictly below a,
and (for comparison) the first-surviving choice."""
import sys,json,pickle,time,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from multiprocessing import Pool
import huac_structure_trio_codex as H
from huac_structure_trio_codex import Ctx,Z,ONE,Y,lt,summ,cs,sumN
def chain(C,m):
 r=[m]
 while True:
  p=C.e.par(1,r[-1])
  if p is None:return r
  r.append(p)
def supp(A,B):return set(summ(A))<=set(summ(B))|{ONE}
def run(batch):
 cnt=collections.Counter();ex={}
 def note(tag,C,d):
  cnt[tag]+=1
  if tag not in ex or len(C.M)<len(ex[tag]['M']):
   d=dict(d);d['M']=''.join('(%d,%d,%d)'%t for t in C.M);ex[tag]=d
 for mm in batch:
  C=Ctx([tuple(t) for t in mm])
  if not C.ok:cnt['eval_FAIL']+=1;continue
  for n in range(len(C.M)):
   k=C.upg(n)
   if k is None or k>=n:continue
   cnt['anc_upg']+=1
   m=C.e.par(1,k);V=C.v(m);W=C.bumpW(k)
   danger=any(g!=Z for q in summ(V) if lt(q,W) for g in cs(Z,q))
   js=[j for j in C.ch(k) if C.M[j]==C.e.bump(k)]
   ch=chain(C,m)
   info={'n':n,'k':k,'m':m,'chain':ch,'V':Y.tstr(V),'W':Y.tstr(W)}
   res='nolast'
   if js and C.ch(js[-1]):
    j=js[-1];c=C.ch(j)[-1];info.update(j=j,c=c)
    ai=[i for i,a in enumerate(ch) if C.M[c][1]==C.M[a][1] and C.M[c][2]==0 and C.M[a][2]==0]
    if c>=n:res='c_ge_n'
    elif not ai:res='noreturn'
    else:
     i=ai[0];a=ch[i];info.update(a=a,i=i)
     st=C.e.par(1,c)==C.e.par(1,a) and C.upg(c)==C.upg(a)
     if not st:note('STRUCT_FAIL.danger%s'%danger,C,info)
     if C.v(c)!=C.v(a):note('VALUE_EQ_FAIL',C,info)
     sp=supp(V,C.v(a))
     step=True
     for x in ch[:i]:
      t=C.upg(x)
      if C.M[x][1]!=0 and C.M[x][2]==0 and t is not None and not supp(Y.last(C.v(t)),C.v(a)):step=False
      if C.M[x][2]!=0:step=False;cnt['chain_bump_col']+=1
     res='ret%d'%min(i,2)
     cnt['supp_%s.danger%s'%(sp,danger)]+=1
     cnt['step_%s.danger%s'%(step,danger)]+=1
     if danger and not sp:note('SUPP_FAIL_danger',C,info)
     if danger and not step:note('STEP_FAIL_danger',C,info)
   cnt['%s.danger%s.zero%s'%(res,danger,W[0]==Z)]+=1
   if danger and W[0]!=Z and not res.startswith('ret'):note('NOWIT_'+res,C,info)
 return dict(cnt),ex
if __name__=='__main__':
 names=sys.argv[1:];rep={}
 with Pool(4) as pool:
  for nm in names:
   mats=pickle.load(open(H.SETD/(nm+'.pkl'),'rb'));cnt=collections.Counter();ex={};t0=time.time()
   for cc,ee in pool.imap(run,(mats[i:i+50] for i in range(0,len(mats),50)),chunksize=1):
    cnt.update(cc)
    for t,e in ee.items():
     if t not in ex or len(e['M'])<len(ex[t]['M']):ex[t]=e
   rep[nm]={'counts':dict(cnt),'ex':ex,'sec':time.time()-t0};print(nm,dict(sorted(cnt.items())),flush=True)
   json.dump(rep,open('/home/koteitan/proofs/trio/tmp/wf/WfHUAC/deep_exact_%s.json'%'_'.join(names),'w'),indent=1)
