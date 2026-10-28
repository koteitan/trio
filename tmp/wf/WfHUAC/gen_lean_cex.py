"""Emit Lean tables (o, v, ranks) for the canonical valuation of a matrix (Ctx)."""
import sys,re,json
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from huac_structure_trio_codex import Ctx,Z,ONE,Y
M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',sys.argv[1])]
C=Ctx(M);assert C.ok
def L(t):
 if t==Z:return 'z'
 return '(psi %s %s %s)'%(L(t[0]),L(t[1]),L(t[2]))
N=len(M)
deps={}
for i in range(N):
 deps[('o',i)]=[('v',i)]+[('o',c) for c in C.CL(i)]
 d=[]
 if M[i][1]!=0:
  p=C.e.par(1,i)
  if p is not None:d.append(('v',p))
  if M[i][2]==0:
   k=C.upg(i)
   if k is not None:d.append(('v',k))
  else:
   for j in C.ch(i):
    if M[j]==C.e.bump(i):d+= [('o',k) for k in C.ch(j)]
 deps[('v',i)]=d
rank={}
def r(x):
 if x in rank:return rank[x]
 rank[x]=1+max([r(y) for y in deps[x]],default=0);return rank[x]
for x in deps:r(x)
print('def oT : List T := ['+', '.join(L(C.o(i)) for i in range(N))+']')
print('def vT : List T := ['+', '.join(L(C.v(i)) for i in range(N))+']')
print('def rkO : List Nat := '+str([rank[('o',i)] for i in range(N)]))
print('def rkV : List Nat := '+str([rank[('v',i)] for i in range(N)]))
