# -*- coding: utf-8 -*-
"""H10 (3d): 対照。**破れていない**対でも ps / first / F は写しごとに食い違うのか。

破れている対と同じやり方で、写し a の柱と写し a-1 の対応する柱を全部くらべる。
"""
import sys, pickle
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, rows3L
from h10L3 import seg, L_at, diff
from core import expand, show

def fields(E, rec, off, bp, r):
    x,y=L_at(rec,off-bp),L_at(rec,off)
    if x is None or y is None: return None
    dd=E[off][0]-E[off-bp][0]
    b=[]
    if diff(x['L'][:-1] if x['L'] else x['L'], y['L'], bp) is not None: b.append('L')
    if x['F']!=y['F']: b.append('F')
    if y['d']-x['d']!=dd: b.append('d')
    if x['ps']!=y['ps']: b.append('ps')
    if x['first']!=y['first']: b.append('first')
    if x['force']!=y['force']: b.append('force')
    return tuple(b)

def run(lim=6, nmax=3):
    A=sorted(rows3.gen3('BMS',lim,zcap=1), key=rows3.key)
    c=Counter()
    for M in A:
        S=tuple(map(tuple,M)); sg=seg(S)
        if sg is None: continue
        r,bp,delta,t=sg
        E=[tuple(x) for x in expand(S,nmax)]
        if r+nmax*bp>len(E): continue
        out,rec=rows3L.b2d3L(list(E))
        for off in range(r+bp, min(r+nmax*bp, len(E))):
            f=fields(E,rec,off,bp,r)
            if f is None: c['取れない']+=1; continue
            for k in (f or ('どれも同じ',)): c[k]+=1
            c['_柱の総数']+=1
    return c

if __name__=='__main__':
    c=run(int(sys.argv[1]) if len(sys.argv)>1 else 6, 3)
    n=c['_柱の総数']
    print('対照: lim=6 の全行列、n=3 の展開、写し 1・2 の全 %d 柱'%n)
    for k,v in c.most_common():
        if k=='_柱の総数': continue
        print('   %-14s %6d  (%.1f%%)'%(k,v,100.0*v/max(n,1)))
