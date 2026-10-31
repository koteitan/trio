"""Generate WfB2SFalse.lean: the 28-column standard Bad2 matrix where the last bump child of k is a leaf."""
import sys,json,re
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from stepfacts3_core_trio_codex import *
import trio
MS="(0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,2,0)(3,2,0)(4,3,1)(5,3,1)(6,3,0)(4,3,1)(5,3,1)(6,2,0)(5,3,1)(5,3,0)(6,4,1)(7,4,1)(8,3,0)(8,2,0)"
M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',MS)];C=Ctx(M);assert len(M)==28
T=tuple(M);N=SRO;steps=[]
for i in range(5000):
 if N==T:break
 for n in range(len(T)+2):
  Q=tuple(map(tuple,trio.expand([list(x) for x in N],n)))
  if Q>=T:
   assert Q<N and len(Q)<2000
   steps.append(n);N=Q;break
 else:raise RuntimeError('No FS index')
assert N==T
deps={}
for i in range(len(M)):
 deps[('o',i)]=[('v',i)]+[('o',c) for c in C.CL(i)]
 d=[]
 if M[i][1]!=0:
  pp=C.e.par(1,i)
  if pp is not None:d.append(('v',pp))
  if M[i][2]==0:
   t=C.upg(i)
   if t is not None:d.append(('v',t))
  else:
   for j in C.ch(i):
    if M[j]==C.e.bump(i):d += [('o',c) for c in C.ch(j)]
 deps[('v',i)]=d
ranks={}
def rank(x):
 if x not in ranks:ranks[x]=1+max([rank(y) for y in deps[x]],default=0)
 return ranks[x]
for x in deps:rank(x)
terms={Z:'z'};defs=[]
def term(t):
 if t not in terms:
  a,b,c=map(term,t);name='t'+str(len(defs));terms[t]=name;defs.append('private def '+name+' : T := psi '+a+' '+b+' '+c)
 return terms[t]
o=[term(C.o(i)) for i in range(len(M))];v=[term(C.v(i)) for i in range(len(M))]
W=term(C.bumpW(19))
print('W',Y.tstr(C.bumpW(19)),'v15',Y.tstr(C.v(15)),'v19',Y.tstr(C.v(19)),file=sys.stderr)
out=open('/home/koteitan/proofs/trio/tmp/wf/WfB2S/false_tables.lean','w')
out.write('def M : Mat := ['+', '.join('(%d, %d, %d)'%t for t in M)+']\n\n')
out.write('def trace : List Nat := ['+', '.join(map(str,steps))+']\n\n')
out.write('\n'.join(defs)+'\n\n')
out.write('def oT : List T := ['+', '.join(o)+']\n')
out.write('def vT : List T := ['+', '.join(v)+']\n')
out.write('def rkO : List Nat := '+str([ranks[('o',i)] for i in range(len(M))])+'\n')
out.write('def rkV : List Nat := '+str([ranks[('v',i)] for i in range(len(M))])+'\n')
out.write('def Wt : T := '+W+'\n')
out.close()
print(len(steps),len(defs))
