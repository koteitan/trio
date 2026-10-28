import sys,json,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import huac_structure_trio_codex as H
from huac_structure_trio_codex import Y,lt,summ,Z
from lhd_exact import comps
d=json.load(open(sys.argv[1]));cnt=collections.Counter();ex={}
for s in d['sets'].values():
 for t,e in s['cases'].items():
  C=H.Ctx([tuple(c) for c in e['matrix']]);x=e['x'];k=e['k'];V=C.vOpt1(x-1);W=C.bumpW(k);vk=C.v(k)
  ab=[q for q in summ(V) if lt(q,W)];dang=any(g!=Z for q in ab for g in comps(Z,q))
  key=(e['e1g'],Y.tstr(V),Y.tstr(W),dang);cnt[key]+=1;ex.setdefault(key,t)
for k,v in cnt.most_common(): print(v,k,ex[k][:200])
