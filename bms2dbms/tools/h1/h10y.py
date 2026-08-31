# -*- coding: utf-8 -*-
"""H10 (3c): ずれた柱で、写し a と写し a-1 の**どの持ち回り量**がちがうか。

記録している量: L（梯子）/ F（行 1 ユニットの先頭フラグ）/ d（行 0 の深さ）/
ps（親のラベル）/ pw（親の影）/ first / force。
d は写しごとに行 0 の持ち上げ delta[0] だけ増えるのが正しいので、その分を引く。
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
bad=sorted(pickle.load(open('/tmp/h1work/img54p.pkl','rb')), key=lambda e:(len(e[0]),e[0],e[1]))
c=Counter(); why_c=Counter()
for A,m,T in bad:
    S=tuple(map(tuple,A)); T=tuple(map(tuple,T)); sg=seg(S)
    if sg is None: continue
    r,bp,delta,t=sg
    best=None
    for n in range(1,9):
        E=[tuple(x) for x in expand(S,n)]
        if not E: continue
        C,PR=provc.b2d3p(list(E)); k=lcp(C,T)
        if best is None: best=(k,n,E,C,PR)
        if len(C)>=len(T): best=(k,n,E,C,PR); break
    k,n,E,C,PR=best
    if k>=len(PR): c['ずれが記録の外']+=1; continue
    off,why=PR[k][1],PR[k][2]
    if off < r+bp: c['ずれは写しの前か写し 0']+=1; continue
    out,rec=rows3L.b2d3L(list(E))
    x,y=L_at(rec,off-bp),L_at(rec,off)
    if x is None or y is None: c['対応する柱が取れない']+=1; continue
    dd = E[off][0]-E[off-bp][0]        # この柱の行 0 の持ち上げ
    bad_f=[]
    if diff(x['L'][:-1] if x['L'] else x['L'], y['L'], bp) is not None: bad_f.append('L')
    if x['F']!=y['F']: bad_f.append('F')
    if y['d']-x['d']!=dd: bad_f.append('d')
    if (y['ps'][0]-x['ps'][0], y['ps'][1]-x['ps'][1])!=(0,0): bad_f.append('ps')
    if x['first']!=y['first']: bad_f.append('first')
    if x['force']!=y['force']: bad_f.append('force')
    c[tuple(bad_f) if bad_f else ('どれも同じ',)]+=1
    why_c[(tuple(bad_f) or ('同じ',), why)]+=1
print('破れ %d 対のうち、ずれた柱で食い違った持ち回り量:'%len(bad))
for k,v in c.most_common(): print('   %-40s %d'%(str(k),v))
print()
print('（食い違った量, 条項 why）:')
for k,v in why_c.most_common(16): print('   %-52s %d'%(str(k),v))
