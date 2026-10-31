import sys,re,json
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQnE')
import analyze as A
from collections import Counter
mats=set()
for l in open('/home/koteitan/proofs/trio/tmp/wf/WfInvX/fam.jsonl'):
    r=json.loads(l)
    for k,L in r.get('ex',{}).items():
        if k in ('ads','tplos'):
            for w in L: mats.add(tuple(tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',w[1])))
print(len(mats))
tot=Counter()
for M in sorted(mats,key=len):
    c,e=A.analyze(list(M),(2,3,4,5),lhd=False); c2,e2=A.fields(list(M))
    print(len(M),dict(c),dict(c2),list(e),list(e2))
