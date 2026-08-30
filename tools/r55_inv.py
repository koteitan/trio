"""`M[0]`（第 0 列）が `oper` / `Pred` / `graft` で**不変**か。
不変なら、どの健全な反証器も底 `lev M[0] > u` しか使えない。"""
import sys, random
from collections import Counter
sys.path.insert(0,'/home/koteitan/proofs/dbms/tools')
import trio
sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
from r49 import Wup
rng=random.Random(7)
COLS=[(a,b,c) for a in range(7) for b in range(7) for c in range(2)]
c=Counter(); bad=[]
for _ in range(60000):
    M=[rng.choice(COLS) for _ in range(rng.randint(2,7))]
    for n in range(1,7):
        E=[tuple(x) for x in trio.expand(list(M),n)]
        if not E: c['空になった']+=1; continue
        if tuple(E[0])==tuple(M[0]): c['oper: 第 0 列は不変']+=1
        else:
            c['**oper: 第 0 列が変わった**']+=1
            if len(bad)<5: bad.append((M,n,E))
    D=M[:-1]
    if D:
        c['Pred: 第 0 列は不変' if tuple(D[0])==tuple(M[0]) else '**Pred: 変わった**']+=1
    # graft M z, z = [(0,0,0)] （based、[] in W m の次に安い証明書）
    G=M[:-1]+[(M[-1][0],0,0)]
    c['graft: 第 0 列は不変' if tuple(G[0])==tuple(M[0]) else '**graft: 変わった**']+=1
for k in sorted(c,key=str): print('   %-30s %d'%(k,c[k]))
for M,n,E in bad: print('   ',M,n,E)
# Wup も同じ退化か
print('== Wup の監査（refute と同じ問い）')
def lev(x): return 2*x[1]+x[2]
memo={}; d=Counter()
for _ in range(4000):
    M=tuple(rng.choice(COLS) for _ in range(rng.randint(1,6))); u=rng.randint(0,4)
    r=Wup(M,u,8,memo,3,40)
    if r is None: d['未判定']+=1; continue
    d['判定できた']+=1
    d['**Wup(M,u)==False  <=>  lev M[0] > u**' if ((r is False)==(lev(M[0])>u)) else '食い違い']+=1
for k in sorted(d,key=str): print('   %-38s %d'%(k,d[k]))
