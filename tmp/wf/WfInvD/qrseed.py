import sys,re
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from probe_inv3_prefix import Ctx,Z,ONE,lt,le
from lhd_exact import lhd,lhdE,comps
import ytosk_eval as Y
M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',sys.argv[1])]
C=Ctx(M);T=Ctx(M[:-1]);x=len(M)-1;r=x-1
print('P0 x',C.e.par(0,x),'P1 x',C.e.par(1,x),'upg r',C.upg(r))
o,o1,v,v1=C.o(r),T.o(r),C.v(r),T.v(r)
for n,t in [('o',o),("o'",o1),('v',v),("v'",v1)]:print(n,Y.tstr(t))
print('lhd(o\',o)',lhd(o1,o),'lhdE',lhdE(o1,o))
w=o1[0];print("w'<v",lt(w,v),'SmallSelf(w\')',all(lt(g,(w,Z,Z)) for g in comps(Z,w)),[Y.tstr(g) for g in comps(Z,w) if not lt(g,(w,Z,Z))])
