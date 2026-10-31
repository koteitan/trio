import sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from probe_inv3_prefix import Ctx, Z, ONE, fsD, holelev, lt, summ, ohole, Y as YE
import trio
ts=YE.tstr
N=[(0,0,0),(1,1,1),(2,1,1),(3,1,0),(1,1,1),(2,1,1),(3,0,0),(4,1,1),(5,1,1),(6,0,0),(7,1,1),(8,1,1),(9,0,0),(10,1,1),(11,1,1),(11,1,0),(12,1,0),(13,0,0),(10,0,0),(2,1,0),(3,2,1),(4,2,1),(5,0,0),(6,1,1),(7,1,1),(8,1,0)]
for n in (2,3):
  E=[tuple(c) for c in trio.expand([list(c) for c in N],n)]
  print('n',n,''.join('(%d,%d,%d)'%c for c in E))
  C=Ctx(E)
  for i in range(19,len(E)):
    print(i,E[i],'p1',C.e.par(1,i),' v',ts(C.v(i)),' o',ts(C.o(i)))
