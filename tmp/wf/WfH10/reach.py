"""Find an explicit expansion trace SRO -> target (greedy, as codex h10_u3_reach). Usage: reach.py '<matrix>' OUT.json"""
import sys,json,time
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from h10_u3_trio_codex import trio
SRO=((0,0,0),(1,1,1),(2,1,1),(3,1,0),(2,0,0))
s=sys.argv[1];T=tuple(tuple(map(int,t.split(','))) for t in s.strip('()').split(')(') )
M=SRO;steps=[];reason='step limit'
for i in range(5000):
 if M==T:reason='reached';break
 found=False
 for n in range(len(T)+2):
  N=tuple(trio.expand(list(M),n))
  if N>=T:
   if not N<M:reason='nondecreasing';break
   if len(N)>2000:reason='length';break
   steps.append({'n':n,'matrix':N});M=N;found=True;break
 if not found:
  if reason=='step limit':reason='no expansion'
  break
print({'reached':M==T,'reason':reason,'steps':len(steps),'maxlen':max([5]+[len(s['matrix']) for s in steps])})
json.dump({'target':T,'reached':M==T,'steps':steps},open(sys.argv[2],'w'))
