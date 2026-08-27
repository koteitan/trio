# -*- coding: utf-8 -*-
"""aw2 が壊す site（浅くすべき）と aw2 が正しく deep と言う site を分ける。"""
import sys, pickle
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
from h6feat import atoms
from rows3 import copy_head, term_top
from core import show

POS = pickle.load(open('/tmp/h1work/aw2broke.pkl','rb'))
tab, cur, dec, want = pickle.load(open('/tmp/h1work/h6tab.pkl','rb'))

def aw_deep2(Mo, off):
    n=len(Mo); p=tuple(Mo[off])
    g=lambda i: tuple(Mo[i]) if 0<=i<n else (-9,-9,-9)
    ch=[t for t in range(n) if copy_head(Mo,t)]
    blk_ge5 = len(ch)>=2 and (ch[1]-ch[0])>=5
    nx2_z = g(off+2)[2] > 0
    pv3_r1_eq = g(off-3)[1] == p[1]
    th=0
    for t in range(off-1,-1,-1):
        if term_top(Mo,t): th=t; break
    zblk1 = sum(1 for t in range(th,off) if Mo[t][2]>0)==1
    return ((not blk_ge5 and nx2_z) or (pv3_r1_eq and not zblk1))

NEG = [k for k in tab
       if dec[k].get('shallow') is not None
       and dec[k]['why'].startswith('after_w')
       and aw_deep2(k[0], k[1]) and not tab[k]]   # aw2 が deep と言い、それが正しい
print('正例（aw2 が壊す）%d / 負例（deep が正しい）%d' % (len(POS), len(NEG)))
X,Y,META,names=[],[],[],None
for k,lab in [(p,True) for p in POS]+[(n,False) for n in NEG]:
    a=atoms(k[0],k[1])
    if names is None: names=sorted(a)
    X.append(tuple(a[nm] for nm in names)); Y.append(lab); META.append(k)
pickle.dump((names,X,Y,META), open('/tmp/h1work/h8sep.pkl','wb'))
d={}; conf=0
for x,y in zip(X,Y):
    if x in d and d[x]!=y: conf+=1
    d[x]=y
print('相異なるベクトル %d  ラベルの矛盾 %d' % (len(d), conf))
