import sys,re
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from probe_inv3_prefix import Ctx,Z,ONE,lt,le,isOT
from lhd_exact import lhd,lhdE,comps
import probe_dropres as D, ytosk_eval as Y
M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',sys.argv[1])];i=int(sys.argv[2])
C=Ctx(M);T=Ctx(M[:-1]);x=len(M)-1
print('x',M[x],'i',i,M[i],'P0 i',C.e.par(0,i),'P1 i',C.e.par(1,i),'upg i',C.upg(i),'P0 x',C.e.par(0,x))
a,b=T.v(i),C.v(i);p=C.e.par(0,i)
print("v'",Y.tstr(a));print('v ',Y.tstr(b));print('v(P0 i)',Y.tstr(C.v(p)))
print('lhdE',lhdE(a,b),'lt',lt(a,b),'CS',D.CS(a),'WCS',D.WCS(C.v(p),a))
print('counted ch',[c for c in C.ch(i) if C.counted(i,c)])
