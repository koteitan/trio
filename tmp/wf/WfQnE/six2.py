import sys,re,json
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQnE')
import analyze as A
mats=set()
for l in open('/home/koteitan/proofs/trio/tmp/wf/WfInvX/fam.jsonl'):
    r=json.loads(l)
    for k,L in r.get('ex',{}).items():
        if k in ('ads','tplos'):
            for w in L: mats.add(tuple(tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',w[1])))
for M in sorted(mats,key=len):
    c,e=A.primary(list(M),(2,3,4,5)); print(len(M),dict(c),{k:v[1:] for k,v in e.items()})
