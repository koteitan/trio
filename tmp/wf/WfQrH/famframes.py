"""Family-derived q = r frames: for every member M of the 15 family pkls (WfInvX/fam.py) and N in {M, M[2], M[3]},
every prefix N[:x+1] with row 2 of x = 0, row 1 != 0, P1 x = P0 x (trio.parent, read from N). Deduplicated, M < SRO.
usage: nice -n 15 python3 famframes.py OUT.pkl"""
import sys,pickle
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvX');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import trio
from fam import FAMS,W
from probe_inv2 import SRO
from probe_inv3_prefix import Ctx
out=set()
for f in FAMS:
    for M in pickle.load(open(W+f,'rb')):
        M=[tuple(c) for c in M]
        for n in (1,2,3):
            N=M if n==1 else [tuple(c) for c in trio.expand([list(c) for c in M],n)]
            for x in range(1,len(N)):
                if N[x][2]!=0 or N[x][1]==0:continue
                r=trio.parent(N,1,x)
                if r is None or trio.parent(N,0,x)!=r:continue
                P=tuple(N[:x+1])
                if list(P)<SRO:out.add(P)
    print(f,len(out),flush=True)
pickle.dump(sorted(out,key=lambda P:(len(P),P)),open(sys.argv[1],'wb'))
