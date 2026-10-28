"""Greedy Std.exp trace from SRO to the 48-column HUACShape counterexample (same method as codex h10_u3_reach)."""
import sys,json,re
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import trio
SRO=((0,0,0),(1,1,1),(2,1,1),(3,1,0),(2,0,0))
T=tuple(tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',sys.argv[1]))
M=SRO;steps=[];reason='step limit'
for i in range(5000):
 if M==T:reason='reached';break
 found=False
 for n in range(len(T)+2):
  N=tuple(map(tuple,trio.expand([list(x) for x in M],n)))
  if N>=T:
   if not N<M:reason='nondecreasing';break
   if len(N)>2000:reason='length';break
   steps.append(n);M=N;found=True;break
 if not found:break
print(json.dumps({'reached':M==T,'reason':reason,'trace':steps,'len':len(steps)}))
