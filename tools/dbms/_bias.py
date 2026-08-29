import sys, itertools, time
sys.path.insert(0,'/home/koteitan/proofs/dbms/tools')
from collections import Counter
from winw import inW2
from r126 import srow, hasP
print('### R126b 判定器の偏りの検算 —— 孤児 / 非孤児 別の判定率（教訓 12: バジェット）')
print('  疑い: 孤児の oper は Pred（末尾を剥がすだけ）で再帰が浅い ⟹ 判定器が通りやすい')
for cm in (1,2):
  for L in (2,3):
    for depth in (3,4,6,8):
        COL=[(d,b,c) for d in range(4) for b in range(3) for c in range(cm+1)]
        memo={}; c=Counter(); t0=time.time()
        for root in COL:
            for t in itertools.product([x for x in COL if x[0]>root[0]], repeat=L-1):
                Q=[root]+list(t); k='孤児' if not hasP(Q) else '非孤児'
                c[(k,'箱')]+=1
                if any(inW2(Q,a,depth,memo,14) is True for a in range(0,8)):
                    c[(k,'W確実')]+=1
        line=f'  行2<={cm} |Q|={L} depth={depth}: '
        for k in ('孤児','非孤児'):
            b=c[(k,'箱')]; w=c[(k,'W確実')]
            line+=f'{k} {w:6d}/{b:6d} = **{100*w/max(b,1):5.1f}%**   '
        print(line+f'[{time.time()-t0:.1f}s]')
