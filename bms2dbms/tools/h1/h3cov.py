# -*- coding: utf-8 -*-
"""汎用: (names, X, Y) から fp=0 の連言を全部集めて正例を覆う。"""
import sys, pickle, time
F = sys.argv[1] if len(sys.argv)>1 else '/tmp/h1work/ct_feat.pkl'
MAXT = int(sys.argv[2]) if len(sys.argv)>2 else 3
names, X, Y, META = pickle.load(open(F,'rb'))
n=len(Y); FULL=(1<<n)-1
COLS=[]
for i in range(len(names)):
    v=0
    for r,x in enumerate(X):
        if x[i]: v|=(1<<r)
    COLS.append(v)
YB=0
for r,y in enumerate(Y):
    if y: YB|=(1<<r)
NY=FULL^YB; pc=lambda v: bin(v).count('1'); POS=pc(YB)
LIT=[]
for i,nm in enumerate(names):
    LIT.append((nm,COLS[i])); LIT.append(('!'+nm, FULL^COLS[i]))
L=len(LIT)
cands=[]; t0=time.time()
def rec(idx, b, lab, d):
    if b and not (b & NY):
        if b & YB: cands.append((b & YB, lab, d))
        return
    if d >= MAXT: return
    for k in range(idx, L):
        nk, bk = LIT[k]
        b2 = b & bk if b is not None else bk
        if b2 == 0: continue
        rec(k+1, b2, (lab + ' & ' + nk) if lab else nk, d+1)
rec(0, FULL, '', 0)
print('fp=0 の連言 %d 個  %.0fs  （正例 %d / 負例 %d）' % (len(cands), time.time()-t0, POS, pc(NY)))
cands.sort(key=lambda t:(-pc(t[0]), t[2]))
red=[]; seen=set()
for c,l,s in cands:
    if c in seen: continue
    seen.add(c); red.append((c,l,s))
print('相異なる覆い %d 個' % len(red))
for c,l,s in red[:12]: print('   %-56s 覆い %d/%d' % (l, pc(c), POS))
sel=[]; cov=0
while cov!=YB and len(sel)<6:
    best=max(red,key=lambda t:pc(t[0]&~cov)) if red else None
    if best is None: break
    g=pc(best[0]&~cov)
    if g==0: break
    sel.append(best); cov|=best[0]
    print('   +%-54s 新規 %3d  累計 %d/%d' % (best[1],g,pc(cov),POS))
print('貪欲 %d 選言で 覆い %d/%d  残り %d' % (len(sel), pc(cov), POS, POS-pc(cov)))
pickle.dump(red, open(F.replace('.pkl','_cov.pkl'),'wb'))
