import os, sys, random
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import trio, ytosk_eval as Y, probe_raw as P
# usage: python3 tools/probe_fs_reach.py {2|3} [max index] [max depth]  -- is eval(M[n]) = eval(M)[m1]...[mk] ?
from ebocf_fs import fs, cof
from collections import Counter
START=P.SRO if sys.argv[1]=='3' else [(0,0,0),(1,1,0),(2,2,0),(3,3,0),(4,4,0)]
MAXM=int(sys.argv[2]) if len(sys.argv)>2 else 5
DEPTH=int(sys.argv[3]) if len(sys.argv)>3 else 4
def step(t):
    cf=cof(t)
    if cf is None: return []
    if cf[0]=='1': return [fs(t,0)]
    if cf[0]=='w': return [fs(t,m) for m in range(MAXM+1)]
    return []
def reach(t,u):
    # BFS keeping only terms >= u
    front={t}; seen={t}
    for d in range(DEPTH+1):
        if u in front: return d
        nxt=set()
        for s in front:
            for s2 in step(s):
                if s2 not in seen and not Y.lt(s2,u):
                    seen.add(s2); nxt.add(s2)
        front=nxt
        if len(seen)>20000: return None
    return None
random.seed(5)
mats=set()
for _ in range(300):
    m=START
    for _ in range(40):
        n=random.randint(0,3); m2=trio.expand(m,n)
        if not m2 or len(m2)>20: continue
        mats.add(tuple(m2)); m=m2
c=Counter(); ex=[]
for m in list(mats)[:900]:
    M=list(m)
    if len(M)<2: continue
    t=Y.Ev(M).value()
    if t is None: continue
    for n in range(1,4):
        u=Y.Ev(trio.expand(M,n)).value()
        d=reach(t,u)
        c['depth %s'%d if d is not None else 'not found']+=1
        if d is None and len(ex)<3: ex.append((''.join('(%d,%d,%d)'%x for x in M),n,Y.tstr(t),Y.tstr(u)))
print(sorted(c.items()))
for e in ex: print(e)
