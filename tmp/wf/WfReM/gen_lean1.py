import sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import trio
from graft import M36
from huac_structure_trio_codex import Ctx,Y,lt,summ
from lhd_exact import lhd
N=[tuple(c) for c in trio.expand([list(c) for c in M36],3)]
N2=[tuple(c) for c in trio.expand([list(c) for c in M36],2)]
print('-- take36 = M[2]:',N[:-1]==N2, file=sys.stderr)
def L(t):
 if not t:return 'z'
 return '(psi %s %s %s)'%(L(t[0]),L(t[1]),L(t[2]))
C=Ctx(N);T=Ctx(N[:-1])
print('def N : Mat := ['+', '.join('(%d, %d, %d)'%c for c in N)+']')
print('def ρO : List T := ['+', '.join(L(C.o(i)) for i in range(len(N)))+']')
print('def ρV : List T := ['+', '.join(L(C.v(i)) for i in range(len(N)))+']')
W=C.bumpW(32);WT=T.bumpW(32)
qs=[q for q in summ(C.vOpt1(32)) if not lt(q,WT) and lt(q,W)]
print('-- candidates',len(qs),[lhd(q,W) for q in qs],file=sys.stderr)
print('def s : T := '+L(qs[0]))
