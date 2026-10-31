"""Expansion + last-column graft family from the 94 case-(b) lower-row big-head frames (probe_b3_grow.json)."""
import json,pickle,re,subprocess,sys
sys.path[:0]=['tools','tmp/codex','tmp/claude']
import trio
SRO=((0,0,0),(1,1,1),(2,1,1),(3,1,0),(2,0,0))
def mt(M):return ''.join('(%d,%d,%d)'%tuple(t) for t in M)
d=json.load(open('tmp/wf/WfSrcB/probe_b3_grow.json'))
seeds={tuple(tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',r['matrix_text'])) for r in d['sets']['grow']['examples']['ALL']}
fam=set(seeds);front=set(seeds)
for _ in range(2):
    new=set()
    for M in front:
        for n in range(1,5):
            N=tuple(map(tuple,trio.expand(list(M),n)))
            if len(N)>170:continue
            for k in range(3,len(N)+1):new.add(N[:k])
    front=new-fam;fam|=new;print('grow',len(front),len(fam),flush=True)
cand=set()
for M in seeds:
    x=len(M)-1;P=M[:x]
    for a in range(1,M[x][0]+2):
        for b in range(0,M[x-1][1]+3):
            N=P+((a,b,1),)
            if N<SRO and N not in fam:cand.add(N)
good=0
for N in sorted(cand):
    if subprocess.run(['./bms','-s',mt(N)],capture_output=True,text=True).stdout.strip()=='1':fam.add(N);good+=1
print('graft cand',len(cand),'std',good,'total',len(fam),flush=True)
pickle.dump([list(M) for M in fam],open('tmp/wf/WfSrcB/growP.pkl','wb'))
