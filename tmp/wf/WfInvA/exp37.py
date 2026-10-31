import sys,re
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import trio
from probe_inv3_prefix import Ctx
from ytosk_eval import tstr
s=sys.argv[1];I=[int(a) for a in sys.argv[2].split(',')];n=int(sys.argv[3])
M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',s)]
N=[tuple(c) for c in trio.expand([list(c) for c in M],n)]
print(''.join('(%d,%d,%d)'%c for c in N))
C=Ctx(N);CM=Ctx(M)
x=len(M)-1;r=CM.e.par(1,x);L=x-r
print('r',r,'L',L,'lenN',len(N))
for i in I:
  for m in range(0,n+1):
    j=i+m*L
    if j<len(N):print('col',j,N[j],'P1',C.e.par(1,j),'v',tstr(C.v(j)),' vP1',tstr(C.v(C.e.par(1,j))) if C.e.par(1,j) is not None else '')
