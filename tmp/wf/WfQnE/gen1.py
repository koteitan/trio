"""Data for WfQnE1.lean: true valuations of N[2], N[3] (N = WfInvX1.N)."""
import sys,re
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import trio, ytosk_eval as Y
from probe_inv3_prefix import Ctx,fsD,fs,Z
S='(0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,0,0)(4,1,1)(5,1,1)(6,0,0)(7,1,1)(8,1,1)(9,0,0)(10,1,1)(11,1,1)(11,1,0)(12,1,0)(13,0,0)(10,0,0)(2,1,0)(3,2,1)(4,2,1)(5,0,0)(6,1,1)(7,1,1)(8,1,0)'
M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',S)]
def L(t):
 if not t:return 'z'
 return '(psi %s %s %s)'%(L(t[0]),L(t[1]),L(t[2]))
for n in (2,3):
  E=[tuple(c) for c in trio.expand([list(c) for c in M],n)]; C=Ctx(E)
  print('def N%d : Mat := ['%n+', '.join('(%d, %d, %d)'%c for c in E)+']')
  print('def τ%dO : List T := ['%n+', '.join(L(C.o(i)) for i in range(len(E)))+']')
  print('def τ%dV : List T := ['%n+', '.join(L(C.v(i)) for i in range(len(E)))+']')
