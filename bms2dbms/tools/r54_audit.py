# refute.py 自身の監査（教訓 12 を新しい計器に当てる）
import sys, random
from collections import Counter
sys.path.insert(0,'/home/koteitan/proofs/dbms/tools')
sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
from refute import refute
def lev(c): return 2*c[1]+c[2]
rng=random.Random(20260829)
COLS=[(a,b,c) for a in range(6) for b in range(6) for c in range(2) if b<=a and c<=min(b,1)]
P=[tuple(rng.choice(COLS) for _ in range(rng.randint(1,7))) for _ in range(20000)]
memo={}; c=Counter(); ex=[]
for M in P:
    u=rng.randint(0,4)
    r=refute(M,u,6,memo,4)
    pred = lev(M[0])>u
    if r is None: c['未判定']+=1; continue
    c['判定できた']+=1
    if bool(r)==pred: c['**refute(M,u) == (lev M[0] > u)**']+=1
    else:
        c['食い違い']+=1
        if len(ex)<5: ex.append((M,u,r,pred))
print('標本 20000（refute.py の自己検査と同じ列、長さ 1..7、u=0..4）')
for k in sorted(c,key=str): print('   %-38s %d'%(k,c[k]))
for e in ex: print('   食い違い M=%s u=%d refute=%s lev0>u=%s'%(''.join(map(str,e[0])),e[1],e[2],e[3]))
