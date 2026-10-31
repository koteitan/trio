import sys,re
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/claude')
sys.argv=['x']
import reach as R
from probe_inv3_prefix import Ctx
import hdropB as H
M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',open('ua35.txt').read())]
p=R.reach(M);assert p is not None
def L(t):
 if not t:return 'z'
 return '(psi %s %s %s)'%(L(t[0]),L(t[1]),L(t[2]))
C=Ctx(M)
print('-- trace length',len(p),'P1 33 =',C.e.par(1,33))
print('def N : Mat := ['+', '.join('(%d, %d, %d)'%c for c in M)+']')
print('def trace : List Nat := ['+', '.join(map(str,p))+']')
print('def ρO : List T := ['+', '.join(L(C.o(i)) for i in range(len(M)))+']')
print('def ρV : List T := ['+', '.join(L(C.v(i)) for i in range(len(M)))+']')
print('def r0 : T := '+L(H.summ(C.vOpt1(33))[0]))
