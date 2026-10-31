"""WfInvD graft family around the HDropU-repair witnesses (2026-10-31).
Seeds: the smallest witness of every FAIL / B2X tag in fam2.jsonl and sets.jsonl, plus WfReM1/WfReM3 N.
Gen 1 for each seed and each of its prefixes ending at the last 3 columns:
 (a) WfReM graft.gen_all (a child of every column c, row 1 in 0..e1 c + 2, row 2 in {0,1}, first or last child;
     one-column mutations; append);
 (b) lift: a child (e0 c + 1, a, 1) of c with a in {4, 5, 6} (row-1 value b >= 4);
 (c) a larger sibling before x - 1: (e0, e1 + d, e2) of x - 1 inserted at x - 1, d in {1, 2}.
Gen 2: (a)-(c) on a sample of 300 gen-1 matrices. Kept: bms -s = 1 and < SRO. Output graftD.pkl."""
import sys,json,pickle,random,re,itertools
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfReM')
import graft as G
from multiprocessing import Pool
def P(s):return [tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',s)]
def extra(M):
    M=[tuple(c) for c in M];x=len(M)-1
    for c in range(x):
        for a in (4,5,6):
            col=(M[c][0]+1,a,1)
            for pos in sorted({c+1,G.subend(M,c)}):
                if pos<len(M):yield M[:pos]+[col]+M[pos:]
    if x>=2:
        y=M[x-1]
        for d in (1,2):yield M[:x-1]+[(y[0],y[1]+d,y[2])]+M[x-1:]
def gen(M):
    M=[tuple(c) for c in M];out=set(G.gen_all(M))
    for N in extra(M):
        if G.keep(N):out.add(tuple(N))
    return out
if __name__=='__main__':
    W='/home/koteitan/proofs/trio/tmp/wf/WfInvD/'
    seeds=set()
    for f in sys.argv[1:]:
        for l in open(f):
            d=json.loads(l)
            for k,v in d['ex'].items():
                if 'FAIL' in k or 'B2X' in k:seeds.add(tuple(P(v[1])))
    seeds|={tuple(P(s)) for s in open(W+'extra_seeds.txt').read().split()}
    base=set()
    for M in seeds:
        for j in range(max(4,len(M)-2),len(M)+1):base.add(M[:j])
    print('seeds',len(seeds),'bases',len(base),flush=True)
    g1=set()
    with Pool(4) as p:
        for o in p.imap_unordered(gen,sorted(base)):g1|=o
        print('gen1',len(g1),flush=True)
        random.seed(11);s2=random.sample(sorted(g1),min(300,len(g1)))
        g2=set()
        for o in p.imap_unordered(gen,s2):g2|=o
    allN=sorted(g1|g2|seeds)
    print('gen2 new',len(g2-g1),'total',len(allN),flush=True)
    pickle.dump([list(N) for N in allN],open(W+'graftD.pkl','wb'))
