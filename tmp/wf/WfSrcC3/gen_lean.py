import sys,json
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from huac_structure_trio_codex import Ctx,Y,lt,le,summ,Z
import trio
d=json.load(open('reach_cex36.json'))
s=open('cex36.txt').read().strip()
M=[tuple(map(int,t.split(','))) for t in s.strip('()').split(')(')]
def L(t):
 if not t:return 'z'
 return '(psi %s %s %s)'%(L(t[0]),L(t[1]),L(t[2]))
def tabs(name,N):
 C=Ctx(N);assert C.ok
 print('def %sO : List T := ['%name+', '.join(L(C.o(i)) for i in range(len(N)))+']')
 print('def %sV : List T := ['%name+', '.join(L(C.v(i)) for i in range(len(N)))+']')
 return C
print('def M : Mat := ['+', '.join('(%d, %d, %d)'%c for c in M)+']')
print('def trace : List Nat := ['+', '.join(str(x['n']) for x in d['steps'])+']')
C=tabs('ρ',M)
tabs('τ',M[:-1])
N=[tuple(c) for c in trio.expand([list(c) for c in M],2)]
tabs('σ',N)
q=summ(C.vOpt1(32))[0]
print('def s : T := '+L(q))
