import sys,re,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfB2S');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import fr3
from probe_inv3_prefix import inv_fields
from stepfacts3_core_trio_codex import Ctx
def parse(s):return [tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',s)]
for s in sys.argv[1:]:
 M=parse(s);fr3.ALL=True
 c,e=fr3.run([M]);print({k:v for k,v in c.items() if 'bpTrue' in k})
 C=Ctx(M);bad=collections.Counter();tot=collections.Counter()
 def note(f,ok,info):
  if ok is None:return
  tot[f]+=1
  if not ok:bad[f]+=1
 inv_fields(C,note);print('inv fail',dict(bad),'of',sum(tot.values()))
