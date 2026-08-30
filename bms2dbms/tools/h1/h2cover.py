# -*- coding: utf-8 -*-
import sys, pickle, time
sys.path.insert(0,'/tmp/h1work')
names, X, Y, META = pickle.load(open('/tmp/h1work/sib_feat.pkl','rb'))
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
NY=FULL^YB
pc=lambda v: bin(v).count('1')
POS=pc(YB)
LIT=[]
for i,nm in enumerate(names):
    LIT.append((nm,COLS[i])); LIT.append(('!'+nm, FULL^COLS[i]))
L=len(LIT)
cands=[]
t0=time.time()
for i in range(L):
    ni,bi=LIT[i]
    if not (bi&NY):
        if bi&YB: cands.append((bi&YB, ni, 1))
    for j in range(i+1,L):
        nj,bj=LIT[j]
        b2=bi&bj
        if not (b2&NY):
            if b2&YB: cands.append((b2&YB,'%s & %s'%(ni,nj),2))
            continue
        for k in range(j+1,L):
            nk,bk=LIT[k]
            b3=b2&bk
            if b3 and not (b3&NY):
                cands.append((b3&YB,'%s & %s & %s'%(ni,nj,nk),3))
print('fp=0 の連言 %d 個  %.0fs' % (len(cands), time.time()-t0))
cands.sort(key=lambda t:(-pc(t[0]), t[2]))
red=[]; seen=set()
for c,l,s in cands:
    if c in seen: continue
    seen.add(c); red.append((c,l,s))
print('相異なる覆い %d 個   正例 %d' % (len(red), POS))
for c,l,s in red[:12]:
    print('   %-48s 覆い %d/%d' % (l, pc(c), POS))
sel=[]; cov=0
while cov!=YB and len(sel)<6:
    best=max(red,key=lambda t:pc(t[0]&~cov))
    g=pc(best[0]&~cov)
    if g==0: break
    sel.append(best); cov|=best[0]
    print('   +%-46s 新規 %3d  累計 %d/%d' % (best[1],g,pc(cov),POS))
print('貪欲 %d 選言で 覆い %d/%d' % (len(sel), pc(cov), POS))
pickle.dump(red, open('/tmp/h1work/sib_cov.pkl','wb'))
