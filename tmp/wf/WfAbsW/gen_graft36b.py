import pickle,sys
from multiprocessing import Pool
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfAbsW')
from gen_graft36 import std,cols
G1=pickle.load(open('/home/koteitan/proofs/trio/tmp/wf/WfAbsW/graft36.pkl','rb'))
cands=set()
for B in G1:
    B=list(B)
    for p in range(24,len(B)):
        for col in cols: cands.add(tuple(B[:p]+[col]+B[p:]))
cands=[M for M in cands if M[-1][2]!=0 and M not in set(G1)]
def f(M): return M if std(list(M)) else None
if __name__=='__main__':
    print(len(cands),flush=True)
    with Pool(4) as P: out=[M for M in P.map(f,cands,chunksize=256) if M]
    print(len(out))
    pickle.dump(out,open('/home/koteitan/proofs/trio/tmp/wf/WfAbsW/graft36b.pkl','wb'))
