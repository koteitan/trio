import sys,re
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from probe_inv3_prefix import Ctx,Z,ONE,lt,le,isOT
from lhd_exact import lhd,lhdE,comps
import ytosk_eval as Y
M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',sys.argv[1])]
C=Ctx(M);T=Ctx(M[:-1]);x=len(M)-1
for i in range(x):
    for nm,a,b in (('o',T.o(i),C.o(i)),('v',T.v(i),C.v(i))):
        if a!=b:print(i,M[i],nm,'P0',C.e.par(0,i),'P1',C.e.par(1,i),'upg',C.upg(i),'lhdE',lhdE(a,b),'lt',lt(a,b),"\n   '",Y.tstr(a)[:200],"\n    ",Y.tstr(b)[:200])
