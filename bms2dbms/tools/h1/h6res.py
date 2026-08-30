# -*- coding: utf-8 -*-
"""覆えなかった正例だけを狙って、もっと長い連言（<=5 項）で fp=0 を探す。"""
import sys, pickle, time
F=sys.argv[1]; MAXT=int(sys.argv[2]) if len(sys.argv)>2 else 5
names,X,Y,META = pickle.load(open(F,'rb'))
red = pickle.load(open(F.replace('.pkl','_cov.pkl'),'rb'))
n=len(Y); FULL=(1<<n)-1
YB=0
for r,y in enumerate(Y):
    if y: YB|=(1<<r)
NY=FULL^YB; pc=lambda v: bin(v).count('1')
# 貪欲で覆えたぶんを引く
cov=0
while True:
    best=max(red,key=lambda t:pc(t[0]&~cov)) if red else None
    if best is None or pc(best[0]&~cov)==0: break
    cov|=best[0]
REM = YB & ~cov
print('残っている正例 %d 本' % pc(REM))
cols=[]
for i in range(len(names)):
    v=0
    for r,x in enumerate(X):
        if x[i]: v|=(1<<r)
    if v==0 or v==FULL: continue
    cols.append((names[i],v))
seen={}; c2=[]
for nm,v in cols:
    k=min(v,FULL^v)
    if k in seen: continue
    seen[k]=1; c2.append((nm,v))
LIT=[]
for nm,v in c2:
    if v & REM: LIT.append((nm,v))
    if (FULL^v) & REM: LIT.append(('!'+nm, FULL^v))
L=len(LIT); print('残りに関係するリテラル %d' % L)
best=[None]
t0=time.time(); cnt=[0]
def rec(idx,b,lab,d):
    cnt[0]+=1
    if not (b & REM): return
    if not (b & NY):
        g=pc(b & REM)
        if best[0] is None or g>best[0][0]: best[0]=(g,lab)
        return
    if d>=MAXT: return
    for k in range(idx,L):
        nk,bk=LIT[k]
        b2=b & bk
        if not (b2 & REM): continue
        rec(k+1,b2,(lab+' & '+nk) if lab else nk,d+1)
rec(0,FULL,'',0)
print('探索 %d 節点 %.0fs' % (cnt[0], time.time()-t0))
print('残りを最も多く覆う fp=0 の連言:', best[0])
