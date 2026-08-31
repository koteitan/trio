# -*- coding: utf-8 -*-
"""H10 (3b): 「像が足りない」70 件で、n を増やすと一致がどうなるかを見る。"""
import sys, pickle
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools/g2')
import rows3, provc
from core import expand, show
def lcp(a,b):
    i,n=0,min(len(a),len(b))
    while i<n and a[i]==b[i]: i+=1
    return i
bad=sorted(pickle.load(open('/tmp/h1work/img54p.pkl','rb')), key=lambda e:(len(e[0]),e[0],e[1]))
c=Counter(); shown=0
for A,m,T in bad:
    S=tuple(map(tuple,A)); T=tuple(map(tuple,T))
    ks=[]
    for n in range(1,7):
        E=[tuple(x) for x in expand(S,n)]
        C=rows3.b2d3(list(E)) if E else ()
        ks.append((n,len(C),lcp(C,T)))
    best=max(ks,key=lambda t:t[2])
    if best[0]!=1: continue
    c['n=1 が最良']+=1
    # n=2 は n=1 の像より前でずれるか
    k1,k2=ks[0][2],ks[1][2]
    c['  n=2 は n=1 より短く一致' if k2<k1 else '  n=2 も同じだけ一致']+=1
    if shown<6:
        shown+=1
        print('%-40s m=%d |T|=%d'%(show([list(x) for x in A]),m,len(T)))
        print('    ', ' '.join('n=%d:|C|=%d lcp=%d'%t for t in ks))
print()
for k,v in c.most_common(): print('   %-30s %d'%(k,v))
