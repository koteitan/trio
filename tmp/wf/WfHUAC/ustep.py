"""U-steps of the deep witness: y on the row-1 chain of m strictly below a with upg y = t.
Record P(t) (bump sum of t), last v(t), whether it is in summands v(a), comps domination by v(a)."""
import sys,json,pickle,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from multiprocessing import Pool
import huac_structure_trio_codex as H
from huac_structure_trio_codex import Ctx,Z,ONE,Y,lt,summ,cs,sumN,dom
from deep_exist import chain,supp
def run(batch):
 cnt=collections.Counter();ex={}
 def note(tag,C,d):
  cnt[tag]+=1
  if tag not in ex or len(C.M)<len(ex[tag]['M']):
   d=dict(d);d['M']=''.join('(%d,%d,%d)'%t for t in C.M);ex[tag]=d
 for mm in batch:
  C=Ctx([tuple(t) for t in mm])
  if not C.ok:continue
  for n in range(len(C.M)):
   k=C.upg(n)
   if k is None or k>=n:continue
   m=C.e.par(1,k);V=C.v(m);W=C.bumpW(k)
   if W[0]==Z:continue
   if not any(g!=Z for q in summ(V) if lt(q,W) for g in cs(Z,q)):continue
   js=[j for j in C.ch(k) if C.M[j]==C.e.bump(k)];ch=chain(C,m)
   P=sumN([ONE]+[C.bumpTerm(k,d) for d in C.ch(k)]);found=None
   for j in js:
    if C.bumpTerm(k,j) not in summ(P):continue
    G=sumN([C.o(d) for d in C.ch(j)])
    for c in C.ch(j):
     if c>=n or C.o(c) not in summ(G):continue
     for i,a in enumerate(ch):
      if C.M[c][1]==C.M[a][1] and C.M[c][2]==0 and C.M[a][2]==0 and supp(V,C.v(a)):
       found=(j,c,i,a);break
     if found:break
    if found:break
   if not found:continue
   j,c,i,a=found
   for l,y in enumerate(ch[:i]):
    t=C.upg(y)
    if t is None:continue
    Pt=sumN([ONE]+[C.bumpTerm(t,d) for d in C.ch(t)]);L=Y.last(C.v(t))
    info={'n':n,'k':k,'m':m,'c':c,'a':a,'y':y,'t':t,'l':l,'i':i,'Pt':Y.tstr(Pt),'L':Y.tstr(L),'va':Y.tstr(C.v(a)),'W':Y.tstr(W)}
    cnt['U']+=1
    cnt['Pt_one_%s'%(Pt==ONE)]+=1
    cnt['t_parent_is_a_%s'%(C.e.par(0,t)==a)]+=1
    cnt['L_in_va_%s'%(L in summ(C.v(a)))]+=1
    cnt['dom_L_va_%s'%dom(L,C.v(a))]+=1
    cnt['t_anc_%s'%(t<y)]+=1
    cnt['va_eq_L_%s'%(C.v(a)==L)]+=1
    note('ex_Pt_one_%s_lastl_%s'%(Pt==ONE,l==i-1),C,info)
 return dict(cnt),ex
if __name__=='__main__':
 names=sys.argv[1:];rep={}
 with Pool(4) as pool:
  for nm in names:
   mats=pickle.load(open(H.SETD/(nm+'.pkl'),'rb'));cnt=collections.Counter();ex={}
   for cc,ee in pool.imap(run,(mats[i:i+50] for i in range(0,len(mats),50)),chunksize=1):
    cnt.update(cc)
    for t,e in ee.items():
     if t not in ex or len(e['M'])<len(ex[t]['M']):ex[t]=e
   rep[nm]={'counts':dict(cnt),'ex':ex};print(nm,dict(sorted(cnt.items())),flush=True)
 json.dump(rep,open('/home/koteitan/proofs/trio/tmp/wf/WfHUAC/ustep_%s.json'%'_'.join(names),'w'),indent=1)
