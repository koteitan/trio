import sys,re
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/claude')
sys.argv=['x']
import reach as R
import ytosk_eval as Y
from probe_inv3_prefix import Ctx,lt,fsD,ONE
import hdropB as H
M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',open('adn38.txt').read())]
p=R.reach(M);assert p is not None
def L(t):
 if not t:return 'z'
 return '(psi %s %s %s)'%(L(t[0]),L(t[1]),L(t[2]))
C=Ctx(M);W=C.bumpW(31);V=C.vOpt1(31)
qs=[q for q in H.summ(V) if lt(q,W) and not lt(q,fsD(W,ONE))]
print('-- trace',len(p),'P1 31',C.e.par(1,31),'W',Y.tstr(W),'q',[Y.tstr(q) for q in qs],'fsD',Y.tstr(fsD(W,ONE)))
print('def N : Mat := ['+', '.join('(%d, %d, %d)'%c for c in M)+']')
print('def trace : List Nat := ['+', '.join(map(str,p))+']')
print('def ρO : List T := ['+', '.join(L(C.o(i)) for i in range(len(M)))+']')
print('def ρV : List T := ['+', '.join(L(C.v(i)) for i in range(len(M)))+']')
print('def Wl : T := '+L(W))
print('def q0 : T := '+L(qs[0]))
