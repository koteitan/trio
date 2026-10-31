import sys,pickle,random
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfB2S')
from multiprocessing import Pool
import graft4
D='/home/koteitan/proofs/trio/tmp/wf/WfB2L/'
if __name__=='__main__':
 S=[tuple(map(tuple,N)) for N in pickle.load(open(D+'g36_1.pkl','rb'))]
 cand=[N for N in S if len(N)>=33]
 random.seed(5);sd=random.sample(cand,min(150,len(cand)))
 print('gen2 seeds',len(cand),len(sd),flush=True)
 T=set()
 with Pool(4) as pool:
  for o in pool.imap_unordered(graft4.gen,sd,chunksize=1):T.update(o)
 T=sorted(T-set(S));pickle.dump([list(N) for N in T],open(D+'g36_2.pkl','wb'));print('gen2',len(T),flush=True)
