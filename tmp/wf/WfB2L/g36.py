"""Grafts around the round-6 36-column matrix (WfSrcC3Cex): all prefixes, one-mutation family of each prefix (gen1),
then gen2 from gen1 matrices that have an fr6 frame. Saves g36_1.pkl, g36_2.pkl."""
import sys,pickle,random
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfB2S')
from multiprocessing import Pool
import graft4
D='/home/koteitan/proofs/trio/tmp/wf/WfB2L/'
def parse(s):
 return [tuple(int(v) for v in t.split(',')) for t in s.strip()[1:-1].split(')(')]
M=parse(open('/home/koteitan/proofs/trio/tmp/wf/WfSrcC3/cex36.txt').read().split('\n')[0])
if __name__=='__main__':
 seeds=[tuple(M[:L]) for L in range(4,len(M)+1)]
 S=set(seeds)
 with Pool(4) as pool:
  for o in pool.imap_unordered(graft4.gen,seeds,chunksize=1):S.update(o)
 S=sorted(S);pickle.dump([list(N) for N in S],open(D+'g36_1.pkl','wb'));print('gen1',len(S),flush=True)
 with Pool(4) as pool:
  fr=list(pool.imap(graft4.frames,[list(N) for N in S],chunksize=20))
 cand=[N for N,f in zip(S,fr) if f and len(N)>=30]
 random.seed(5);sd=random.sample(cand,min(150,len(cand)))
 print('gen2 seeds',len(cand),len(sd),flush=True)
 T=set()
 with Pool(4) as pool:
  for o in pool.imap_unordered(graft4.gen,sd,chunksize=1):T.update(o)
 T=sorted(T-set(S));pickle.dump([list(N) for N in T],open(D+'g36_2.pkl','wb'));print('gen2',len(T),flush=True)
