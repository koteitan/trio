# -*- coding: utf-8 -*-
"""fp=0 の連言（<=MAXT 項）で正例を覆う。定数・重複列を先に落とす。"""
import sys, pickle, time
F = sys.argv[1]; MAXT = int(sys.argv[2]) if len(sys.argv)>2 else 3
names, X, Y, META = pickle.load(open(F,'rb'))
n=len(Y); FULL=(1<<n)-1
YB=0
for r,y in enumerate(Y):
    if y: YB|=(1<<r)
NY=FULL^YB; pc=lambda v: bin(v).count('1'); POS=pc(YB)
raw=[]
for i in range(len(names)):
    v=0
    for r,x in enumerate(X):
        if x[i]: v|=(1<<r)
    raw.append((names[i], v))
# 定数を落とす
raw=[(nm,v) for nm,v in raw if v!=0 and v!=FULL]
# 重複（および補集合の重複）を落とす
seen={}; cols=[]
for nm,v in raw:
    key = min(v, FULL^v)
    if key in seen: continue
    seen[key]=nm; cols.append((nm,v))
print('素性 %d -> 定数・重複を落として %d   （正例 %d / 負例 %d）'
      % (len(names), len(cols), POS, pc(NY)))
LIT=[]
for nm,v in cols:
    LIT.append((nm,v)); LIT.append(('!'+nm, FULL^v))
L=len(LIT); print('リテラル %d' % L)
cands=[]; t0=time.time()
def rec(idx,b,lab,d):
    if b and not (b & NY):
        if b & YB: cands.append((b & YB, lab, d))
        return
    if d>=MAXT: return
    for k in range(idx,L):
        nk,bk=LIT[k]
        b2 = b & bk
        if b2==0: continue
        rec(k+1,b2,(lab+' & '+nk) if lab else nk,d+1)
rec(0,FULL,'',0)
print('fp=0 の連言 %d 個  %.0fs' % (len(cands), time.time()-t0))
cands.sort(key=lambda t:(-pc(t[0]), t[2]))
red=[]; seen2=set()
for c,l,s in cands:
    if c in seen2: continue
    seen2.add(c); red.append((c,l,s))
print('相異なる覆い %d 個' % len(red))
for c,l,s in red[:10]: print('   %-58s 覆い %d/%d' % (l, pc(c), POS))
sel=[]; cov=0
while cov!=YB and len(sel)<6:
    best=max(red,key=lambda t:pc(t[0]&~cov)) if red else None
    if best is None: break
    g=pc(best[0]&~cov)
    if g==0: break
    sel.append(best); cov|=best[0]
    print('   +%-56s 新規 %3d  累計 %d/%d' % (best[1],g,pc(cov),POS))
print('貪欲 %d 選言で 覆い %d/%d  残り %d' % (len(sel), pc(cov), POS, POS-pc(cov)))
pickle.dump(red, open(F.replace('.pkl','_cov.pkl'),'wb'))
