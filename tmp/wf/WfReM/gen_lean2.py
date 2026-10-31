import sys,json,re
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from huac_structure_trio_codex import Ctx,Y
from probe_inv3_prefix import sumN,ONE
d=json.load(open('qn46_trace.json'));s=d['witness'][1]
M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',s)]
def L(t):
 if not t:return 'z'
 return '(psi %s %s %s)'%(L(t[0]),L(t[1]),L(t[2]))
C=Ctx(M);T=Ctx(M[:-1]);x=len(M)-1
print('def N : Mat := ['+', '.join('(%d, %d, %d)'%c for c in M)+']')
print('def trace : List Nat := ['+', '.join(map(str,d['trace']))+']')
for nm,CC,NN in (('ρ',C,M),('τ',T,M[:-1])):
 print('def %sO : List T := ['%nm+', '.join(L(CC.o(i)) for i in range(len(NN)))+']')
 print('def %sV : List T := ['%nm+', '.join(L(CC.v(i)) for i in range(len(NN)))+']')
X1=T.pre(41,T.CL(41));t1=X1[0][1]  # X1 = psi(psi(t1)) form: summ last
from fdshcopy_trio_codex import summ
t1=summ(X1)[-1][0]
print('def t1 : T := '+L(t1))
S=Y.add(C.v(41),Y.omega(sumN([ONE]+[C.bumpTerm(42,dd) for dd in C.ch(42) if dd<x])))
from fdshcopy_trio_codex import comp
g=[g for g in comp(C.v(30),S) if not Y.lt(g,X1)][0]
print('def g : T := '+L(g))
for k in (30,34):print('-- CL %d ='%k,C.CL(k))
for c in (34,41):o=C.o(c);print('def s%d : T := %s'%(c,L(o[0])));print('def y%d : T := %s'%(c,L(o[1])))
