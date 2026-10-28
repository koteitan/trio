import sys,json,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import huac_structure_trio_codex as H
from huac_structure_trio_codex import Y,lt,summ,Z
d=json.load(open(sys.argv[1]));cnt=collections.Counter();ex={}
for s in d['sets'].values():
 for t,e in s['cases'].items():
  if e['e1g']<2:continue
  M=[tuple(c) for c in e['matrix']];E=Y.Ev(M);x=e['x'];k=e['k'];g=e['g']
  a=M[x-1][1];mp=E.par(1,x-1);A=E.par(1,g)
  ch=E.children[k];bj=[j for j in ch if M[j]==E.bump(k)];bjc=[j for j in bj if E.children[j]]
  key=('a=e1g',a==M[g][1],'mp=P1g',mp==A,'nch',len(ch),'nbump',len(bj),'nbumpwithkids',len(bjc),'kchild_is_g',ch[-1]==g)
  cnt[key]+=1;ex.setdefault(key,t)
for k,v in cnt.most_common(): print(v,k,ex[k][:300])
