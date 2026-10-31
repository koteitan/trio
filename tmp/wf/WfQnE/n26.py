import sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from probe_inv3_prefix import Ctx, Z, ONE, fsD, holelev, lt, summ, ohole, Y as YE
ts=YE.tstr
N=[(0,0,0),(1,1,1),(2,1,1),(3,1,0),(1,1,1),(2,1,1),(3,0,0),(4,1,1),(5,1,1),(6,0,0),(7,1,1),(8,1,1),(9,0,0),(10,1,1),(11,1,1),(11,1,0),(12,1,0),(13,0,0),(10,0,0),(2,1,0),(3,2,1),(4,2,1),(5,0,0),(6,1,1),(7,1,1),(8,1,0)]
C=Ctx(N); T=Ctx(N[:25])
x=25; r=C.e.par(1,x); print('r',r,'P0',C.e.par(0,x))
seed=T.o(r); print('o_N(r)',ts(C.o(r)),'seed',ts(seed))
for i in range(25):
  print(i,N[i],'p1',C.e.par(1,i),'\n  vN ',ts(C.v(i)),'\n  vT ',ts(T.v(i)),'\n  oN ',ts(C.o(i)),'\n  oT ',ts(T.o(i)))
  if ohole(C.v(i)): print('  fsD(vN,seed)',ts(fsD(C.v(i),seed)))
  if ohole(C.o(i)): print('  fsD(oN,seed)',ts(fsD(C.o(i),seed)))
