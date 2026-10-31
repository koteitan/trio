import sys,re,json,pickle
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQnE')
import analyze as A
mats=set()
for l in open('/home/koteitan/proofs/trio/tmp/wf/WfInvX/fam.jsonl'):
    r=json.loads(l)
    for k,L in r.get('ex',{}).items():
        if k in ('ads','tplos'):
            for w in L: mats.add(tuple(tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',w[1])))
seeds=set(mats)
for M in mats:
    for j in range(4,len(M)):
        if A.frame(list(M[:j])) is not None: seeds.add(M[:j])
print(len(seeds))
pickle.dump(sorted(seeds,key=len),open('/home/koteitan/proofs/trio/tmp/wf/WfQnE/seeds0.pkl','wb'))
