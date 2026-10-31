"""Lean VSmallF (V3DropMain): for every counted child c of i (L = earlier counted children),
every g in comps (v i) (v c) has g <= psi (v c) 0 0 or g <= spArg (v i) 0 (sumN (L.map o))."""
import sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from probe_inv3_prefix import Ctx,Z,le,comps,spa,sumN
def vsmallf(M):
    C=Ctx(M);bad=[]
    for i in range(len(M)):
        cl=C.CL(i);vi=C.v(i)
        for idx,c in enumerate(cl):
            B=spa(vi,sumN([C.o(d) for d in cl[:idx]]));vc=C.v(c)
            for g in comps(vi,vc):
                if not (le(g,(vc,Z,Z)) or le(g,B)):bad.append((i,c));break
    return bad
