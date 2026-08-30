# -*- coding: utf-8 -*-
"""H10 (3): ImgClosedT の破れ 54 個は「梯子 L の漏れ」で説明できるか。

破れ (A, m) について、目標 T = (conv3 A)<m> といちばん長く一致する
候補 A<n> をさがし、**最初にずれた柱**の出どころ off を PROV から引く。
その off が入っている写し a の頭の L が、写し a-1 の頭の L を
（上 1 段を除いて）書き換えていたら「L の漏れで説明できる」と数える。
"""
import sys, pickle
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools/g2')
import rows3, rows3L, provc
from h10L3 import seg, L_at, diff
from core import expand, show

def lcp(a,b):
    i,n=0,min(len(a),len(b))
    while i<n and a[i]==b[i]: i+=1
    return i

bad = pickle.load(open('/tmp/h1work/img54p.pkl','rb'))
bad = sorted(bad, key=lambda e:(len(e[0]),e[0],e[1]))
print('破れ %d 個'%len(bad))
c=Counter(); rows=[]
for A,m,T in bad:
    S=tuple(map(tuple,A)); T=tuple(map(tuple,T))
    best=None
    for n in range(1,9):
        E=[tuple(x) for x in expand(S,n)]
        if not E: continue
        C,PR = provc.b2d3p(list(E))
        k=lcp(C,T)
        if best is None or k>best[0]: best=(k,n,E,C,PR)
    k,n,E,C,PR = best
    if k>=len(T) and len(C)==len(T):
        c['じつは一致（破れの原因は別）']+=1; rows.append((A,m,'一致',None,None)); continue
    if k>=len(PR):
        c['ずれが目標の末尾（像が %d 柱足りない, n=%d）'%(len(T)-len(C),n)]+=1
        rows.append((A,m,'末尾',None,None)); continue
    off, why = PR[k][1], PR[k][2]
    sg=seg(S)
    if sg is None:
        c['写しの構造が取れない']+=1; continue
    r,bp,delta,t=sg
    if off < r + bp:
        c['ずれは写しの前か写し 0']+=1; rows.append((A,m,'写し0前',off,why)); continue
    out,rec=rows3L.b2d3L(list(E))
    x, y = L_at(rec, off-bp), L_at(rec, off)
    if x is None or y is None:
        c['対応する柱の L が取れない']+=1; rows.append((A,m,'L不明',off,why)); continue
    dL = diff(x['L'][:-1] if x['L'] else x['L'], y['L'], bp)
    leak = dL is not None
    c['**L の漏れで説明できる**' if leak else 'L は同変（別の原因）']+=1
    rows.append((A,m,'漏れ' if leak else '同変',off,why))
print()
for k,v in c.most_common(): print('   %-34s %d'%(k,v))
print()
print('内訳（why = ずれた柱の綴りの条項）:')
w=Counter((r[2],r[4]) for r in rows)
for k,v in w.most_common(16): print('   %-46s %d'%(str(k),v))
print()
for A,m,tag,off,why in rows[:10]:
    print('   %-40s m=%d  %s  off=%s why=%s'%(show([list(x) for x in A]),m,tag,off,why))
pickle.dump(rows, open('/tmp/h1work/h10rows.pkl','wb'))
