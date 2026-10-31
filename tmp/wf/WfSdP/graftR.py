"""WfSdP graftR (2026-11-01): graft attack on UAwR. Seeds = matrices of graftD/graftE where the weak absorption case
at x - 1 has domV false (comps of V not dominated by comps of v(x-1); UAwR then needs g <= Om_{V+1}), smallest 40.
gen1 = WfInvD graftD.gen (WfReM graft.gen_all + lifts + sibling) + M[2], M[3] prefixes, on the seeds and their
prefixes ending in the last 3 columns; gen2 = the same on 200 random gen1. Kept bms -s = 1, < SRO. -> graftR.pkl
usage: nice -n 15 python3 graftR.py NPROC"""
import sys,pickle,random
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfDrE');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfSdP')
import graftE as GE
import uawra as uawr
from pv2 import load
from multiprocessing import Pool
def isseed(M):
    c,e=uawr.probe(M)
    return any(k.startswith('weak.') and '.domV=0.' in k for k in c)
def chk(b):return [M for M in b if isseed(M)]
if __name__=='__main__':
    npr=int(sys.argv[1])
    mats=load('/home/koteitan/proofs/trio/tmp/wf/WfInvD/graftD.pkl')+load('/home/koteitan/proofs/trio/tmp/wf/WfDrE/graftE.pkl')
    with Pool(npr) as p:
        S=[M for o in p.imap_unordered(chk,(mats[i:i+200] for i in range(0,len(mats),200))) for M in o]
        S=sorted({tuple(tuple(c) for c in M) for M in S},key=lambda M:(len(M),M))[:40]
        print('seeds',len(S),flush=True)
        base=set()
        for M in S:
            for j in range(max(4,len(M)-2),len(M)+1):base.add(M[:j])
        g1=set()
        for o in p.imap_unordered(GE.gen,sorted(base)):g1|=o
        print('gen1',len(g1),flush=True)
        random.seed(17);s2=random.sample(sorted(g1),min(200,len(g1)))
        g2=set()
        for o in p.imap_unordered(GE.gen,s2):g2|=o
    allN=sorted(g1|g2|set(S))
    print('total',len(allN),flush=True)
    pickle.dump([list(N) for N in allN],open('/home/koteitan/proofs/trio/tmp/wf/WfSdP/graftR.pkl','wb'))
