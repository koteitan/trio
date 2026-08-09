"""(INS): is `Wself` closed under inserting ONE arbitrary column anywhere?

    S in Wself  ==>  S.take q ++ [t] ++ S.drop q  in Wself   (any q, any t)

This is the shortest possible statement of the whole theorem: `[] in Wself`, and
every matrix is built from `[]` by inserting one column at a time, so (INS)
implies `Wself` is everything, which IS trio termination.  At `q = |S|` it is
`(SNOC)`, already wired as `Final.TRIO_terminates_of_snoc`, so (INS) adds no new
core -- it is the same face, stated without any side condition.

Two measurements, both 0 violations:
  * `t` constrained to sit strictly below `S[p]` and inserted at `p+1`:
    1268993 decided, 95254 undecided;
  * `t` and the position completely unconstrained:
    1603817 decided, 84184 undecided.

The decision procedure uses the proved shortcut `snoc_zeroRow2` (a block whose
`dropLast` is row-2-free is in `Wself`) as a base case, which is why it decides
far more than the earlier probes.
"""
import sys, itertools, random
from collections import Counter
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import trio
NS=(1,2); MAXD=11; MAXLEN=44
def lev(c): return 2*c[1]+c[2]
def inW(S,a,d,memo):
    S=tuple(tuple(c) for c in S); key=(S,a)
    if key in memo: return memo[key]
    if len(S)==0: return True
    if len(S)==1:
        r=lev(S[0])<=a; memo[key]=r; return r
    if all(c[2]==0 for c in S[:-1]): 
        r = lev(S[0])<=a; memo[key]=r; return r      # snoc_zeroRow2 / zeroRow2
    if d<=0 or len(S)>MAXLEN: return None
    memo[key]=None; out=True
    for n in NS:
        r=inW(trio.expand(list(S),n),a,d-1,memo)
        if r is False: memo[key]=False; return False
        if r is None: out=None
    memo[key]=out; return out
def inSelf(S,memo):
    if not S: return True
    return inW(S,lev(tuple(S[0])),MAXD,memo)

memo={}; tot=Counter(); ex=[]
rng=random.Random(99991)
COLS=[(x,b,z) for x in range(4) for b in range(3) for z in range(2)]
pop=[]
for L in (2,3,4):
    for S in itertools.product(COLS,repeat=L):
        S=list(S)
        if S[0][0]!=0: continue
        pop.append(S)
for _ in range(30000):
    L=rng.randint(4,6)
    S=[(0,rng.randint(0,3),rng.randint(0,1))]
    for _ in range(L-1): S.append((rng.randint(0,5),rng.randint(0,3),rng.randint(0,1)))
    pop.append(S)
print('pop',len(pop),flush=True)
for S in pop:
    if inSelf(S,memo) is not True: continue
    tot['S ok']+=1
    for q in range(len(S)+1):
        for _ in range(3):
            t=(rng.randint(0,5), rng.randint(0,3), rng.randint(0,1))
            R=S[:q]+[t]+S[q:]
            if len(R)>MAXLEN: continue
            r=inSelf(R,memo)
            if r is None: tot['undecided']+=1; continue
            tot['decided']+=1
            if r is False:
                tot['VIOLATION']+=1
                if len(ex)<6: ex.append((S,q,t,R))
for k in sorted(tot): print(f'  {k:14s} {tot[k]:9d}')
for S,q,t,R in ex: print(f'  VIOL S={S} q={q} t={t}\n    R={R}')
