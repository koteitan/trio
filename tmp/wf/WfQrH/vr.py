import sys,pickle,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from probe_inv3_prefix import Ctx, lt
cnt=collections.Counter()
for f in sys.argv[1:]:
    for M in pickle.load(open(f,'rb')):
        M=[tuple(c) for c in M];x=len(M)-1
        if M[x][2] or not M[x][1]:continue
        C=Ctx(M)
        if not C.ok:continue
        r=C.e.par(1,x)
        if r is None or C.e.par(0,x)!=r:continue
        T=Ctx(M[:x]);cnt['frames']+=1
        cnt['veq' if T.v(r)==C.v(r) else 'vNE']+=1
        cnt['vle' if (T.v(r)==C.v(r) or lt(T.v(r),C.v(r))) else 'vGT']+=1
        cnt['L1' if x==r+1 else 'L>1']+=1
print(dict(cnt))
