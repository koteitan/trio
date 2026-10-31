"""Shortest B2LevS counterexample (from lift1_fail.pkl): expansion trace from SRO and the frame data."""
import sys,json,pickle,subprocess
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from stepfacts3_core_trio_codex import *
import trio
F=pickle.load(open('lift1_fail.pkl','rb'));F=sorted(F,key=lambda M:(len(M),M))
M=[tuple(c) for c in F[0]];C=Ctx(M);n=len(M)-2
s=''.join('(%d,%d,%d)'%t for t in M)
print(s,len(M),subprocess.run(['/home/koteitan/proofs/trio/bms','-s',s],capture_output=True,text=True).stdout.strip())
k=C.upg(n);m=C.e.par(0,k);p=C.e.par(0,n);g=C.e.par(0,p)
print('n',n,'k',k,'m',m,'p',p,'g',g,'ch k',C.ch(k),[(j,M[j],C.ch(j)) for j in C.ch(k)],'M[m]',M[m],'M[k]',M[k])
T=tuple(M);N=SRO;steps=[]
for i in range(5000):
 if N==T:break
 for nn in range(len(T)+2):
  Q=tuple(map(tuple,trio.expand([list(x) for x in N],nn)))
  if Q>=T:
   assert Q<N and len(Q)<2000
   steps.append(nn);N=Q;break
 else:raise RuntimeError('No FS index')
assert N==T
print(len(steps));print('['+', '.join(map(str,steps))+']')
print('['+', '.join('(%d, %d, %d)'%t for t in M)+']')
