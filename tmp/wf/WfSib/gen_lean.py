import sys,json
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfSib')
from huac_structure_trio_codex import Ctx,summ
from bad2_exact_trio_codex import upgabs_all
import trio
from reach0 import reach,parse
s=sys.argv[1]
M=parse(s)
p=reach(M)
def L(t):
 if not t:return 'z'
 return '(psi %s %s %s)'%(L(t[0]),L(t[1]),L(t[2]))
C=Ctx(M);assert C.ok
x=len(M)-1;k=C.upg(x-1)
ok,n,bad=upgabs_all(C.vOpt1(x-1),C.v(k))
W,q=bad[0]
print('def M : Mat := ['+', '.join('(%d, %d, %d)'%c for c in M)+']')
print('def trace : List Nat := ['+', '.join(map(str,p))+']')
print('def ρO : List T := ['+', '.join(L(C.o(i)) for i in range(len(M)))+']')
print('def ρV : List T := ['+', '.join(L(C.v(i)) for i in range(len(M)))+']')
print('def W : T := '+L(W))
print('def q : T := '+L(q))
