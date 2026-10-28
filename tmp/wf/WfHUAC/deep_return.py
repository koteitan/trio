"""Deep return: in dangerous ancestor-upgrade frames, does the chosen grandchild c
return to the row-1 level of some P1-ancestor a_i of m (a_0=m), with P1(c)=P1(a_i),
upg(c)=upg(a_i), row2(c)=row2(a_i)=0 (hence v(c)=v(a_i))?"""
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
def run(batch):
 cnt=collections.Counter();ex={}
 for mm in batch:
  C=Ctx([tuple(t) for t in mm])
  if not C.ok:cnt['eval_FAIL']+=1;continue
  for n in range(len(C.M)):
   k=C.upg(n)
   if k is None or k>=n:continue
   m=C.e.par(1,k);V=C.v(m);W=C.bumpW(k)
   ab=[q for q in summ(V) if lt(q,W)]
   if not any(g!=Z for q in ab for g in cs(Z,q)):continue
   cnt['danger']+=1
   if W[0]==Z:cnt['zero']+=1;continue
   js=[j for j in C.ch(k) if C.M[j]==C.e.bump(k)]
   P=sumN([ONE]+[C.bumpTerm(k,d) for d in C.ch(k)])
   first=next((d for d in js if C.bumpTerm(k,d) in summ(P)),None)
   ch=chain(C,m)
   def ret(c):
    for i,a in enumerate(ch):
     if C.M[c][1]==C.M[a][1] and C.M[c][2]==0 and C.M[a][2]==0 and C.e.par(1,c)==C.e.par(1,a) and C.upg(c)==C.upg(a):return i
    return None
   tag=''
   if first is None:cnt['nofirst']+=1;tag='nofirst'
   elif not C.ch(first):cnt['first_childless']+=1;tag='childless'
   else:
    c=C.ch(first)[0]
    i=ret(c)
    tag='firstc_ret%s'%('None' if i is None else min(i,3))
    cnt[tag]+=1
    if i is not None:
     cnt['vc_eq_va' if C.v(c)==C.v(ch[i]) else 'vc_ne_va']+=1
     cnt['c_lt_n' if c<n else 'c_ge_n']+=1
     # the absorbed dangerous summands not in v(a_i)
     va=set(summ(C.v(ch[i])))
     bad=[q for q in ab if any(g!=Z for g in cs(Z,q)) and q not in va]
     cnt['extra_danger_%d'%min(len(bad),2)]+=1
     # increments of a_0..a_{i-1}
     kinds=[]
     for a in ch[:i]:
      kinds.append('Z' if C.M[a][1]==0 else 'B' if C.M[a][2] else ('U' if C.upg(a) is not None else 'P'))
     cnt['inc_'+''.join(kinds)]+=1
     for a in ch[:i]:
      t=C.upg(a)
      if C.M[a][1]!=0 and C.M[a][2]==0 and t is not None:
       L=Y.last(C.v(t))
       cnt['U_t_'+('anc' if t<a else 'next')]+=1
       cnt['U_last_'+('absorbed' if lt(L,W) else 'kept')]+=1
       cnt['U_last_dangerous_%s'%any(g!=Z for g in cs(Z,L))]+=1
       cnt['U_last_in_va_%s'%(L in va)]+=1
       if lt(L,W) and any(g!=Z for g in cs(Z,L)) :
        tg='Uabsdanger_in_va_%s'%(L in va);cnt[tg]+=1
        if tg not in ex or len(C.M)<len(ex[tg]['M']):
         ex[tg]={'M':''.join('(%d,%d,%d)'%t for t in C.M),'n':n,'k':k,'m':m,'first':first,'c':c,'a':ch[i],'al':a,'t':t,'chain':ch,'V':Y.tstr(V),'W':Y.tstr(W),'L':Y.tstr(L),'va':Y.tstr(C.v(ch[i]))}
   if tag not in ex or len(C.M)<len(ex[tag]['M']):
    ex[tag]={'M':''.join('(%d,%d,%d)'%t for t in C.M),'n':n,'k':k,'m':m,'first':first,'chain':ch,'V':Y.tstr(V),'W':Y.tstr(W)}
 return dict(cnt),ex
if __name__=='__main__':
 names=sys.argv[1:]
 rep={}
 with Pool(4) as pool:
  for nm in names:
   mats=pickle.load(open(H.SETD/(nm+'.pkl'),'rb'));cnt=collections.Counter();ex={}
   for cc,ee in pool.imap(run,(mats[i:i+50] for i in range(0,len(mats),50)),chunksize=1):
    cnt.update(cc)
    for t,e in ee.items():
     if t not in ex or len(e['M'])<len(ex[t]['M']):ex[t]=e
   rep[nm]={'counts':dict(cnt),'ex':ex};print(nm,dict(cnt),flush=True)
 json.dump(rep,open('/home/koteitan/proofs/trio/tmp/wf/WfHUAC/deep_return_%s.json'%'_'.join(names),'w'),indent=1)
