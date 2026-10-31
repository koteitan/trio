import sys,pickle
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfSrcO')
from multiprocessing import Pool
from t2src_a_trio_codex import *
from probe_B import hits
def run(batch):
    out=[]
    for mm in batch:
        M=list(map(tuple,mm));x=len(M)-1
        if x<3:continue
        E=Y.Ev(M);hs=hits(M,E,x)
        if not hs:continue
        C=Ctx(M);T=Ctx(M[:x])
        if not C.ok or not T.ok:continue
        if any(C.o(h[3])!=T.o(h[3]) for h in hs):out.append(M)
    return out
if __name__=='__main__':
    mats=pickle.load(open(sys.argv[1],'rb'))
    if isinstance(mats,dict):mats=mats.get('seeds',[])+mats.get('ext',[])
    res=[]
    with Pool(3) as pool:
        for o in pool.imap_unordered(run,(mats[i:i+500] for i in range(0,len(mats),500))):res+=o
    pickle.dump(res,open(sys.argv[2],'wb'));print(len(res))
