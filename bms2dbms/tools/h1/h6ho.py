# -*- coding: utf-8 -*-
"""ホールドアウト検定: 半分で fp=0 の貪欲被覆を作り、もう半分で測る。"""
import sys, pickle, time
F=sys.argv[1]; MAXT=int(sys.argv[2]) if len(sys.argv)>2 else 3
SEED=int(sys.argv[3]) if len(sys.argv)>3 else 1
names,X,Y,META = pickle.load(open(F,'rb'))
N=len(Y)
idx=list(range(N))
# 決定的な分割（行列の hash で half）
tr=[i for i in idx if hash((META[i][0], META[i][1], SEED)) % 2 == 0]
te=[i for i in idx if i not in set(tr)]
def build(sub):
    n=len(sub); FULL=(1<<n)-1
    YB=0
    for r,i in enumerate(sub):
        if Y[i]: YB|=(1<<r)
    cols=[]
    for c in range(len(names)):
        v=0
        for r,i in enumerate(sub):
            if X[i][c]: v|=(1<<r)
        cols.append(v)
    return FULL, YB, cols
FULL,YB,COLS = build(tr)
NY=FULL^YB; pc=lambda v: bin(v).count('1')
seen={}; keep=[]
for c in range(len(names)):
    v=COLS[c]
    if v==0 or v==FULL: continue
    k=min(v,FULL^v)
    if k in seen: continue
    seen[k]=1; keep.append(c)
LIT=[]
for c in keep:
    LIT.append((c,False,COLS[c])); LIT.append((c,True,FULL^COLS[c]))
L=len(LIT)
cands=[]
def rec(i,b,lab,d):
    if b and not (b&NY):
        if b&YB: cands.append((b&YB,tuple(lab)))
        return
    if d>=MAXT: return
    for k in range(i,L):
        c,neg,bk=LIT[k]
        b2=b&bk
        if b2==0: continue
        rec(k+1,b2,lab+[(c,neg)],d+1)
rec(0,FULL,[],0)
sel=[]; cov=0
while cov!=YB and len(sel)<8:
    best=max(cands,key=lambda t:pc(t[0]&~cov)) if cands else None
    if best is None or pc(best[0]&~cov)==0: break
    sel.append(best[1]); cov|=best[0]
print('学習側 %d 件（正 %d）  選んだ選言 %d 本  学習側の覆い %d/%d'
      % (len(tr), pc(YB), len(sel), pc(cov), pc(YB)))
def pred(i):
    for conj in sel:
        if all((not X[i][c]) if neg else X[i][c] for c,neg in conj): return True
    return False
for nm,sub in (('学習', tr), ('**検定**', te)):
    tp=sum(1 for i in sub if Y[i] and pred(i))
    fp=sum(1 for i in sub if (not Y[i]) and pred(i))
    fn=sum(1 for i in sub if Y[i] and not pred(i))
    tn=sum(1 for i in sub if (not Y[i]) and not pred(i))
    print('   %-8s 正例 %3d 中 当たり %3d / 外し %3d    負例 %4d 中 **誤発火 %3d**'
          % (nm, tp+fn, tp, fn, fp+tn, fp))
