# -*- coding: utf-8 -*-
"""H10 (1d): 書き換えは「梯子のいちばん上の段」だけか。

L の一番上の段は写しの境目そのもので書かれる暫定の段。それを除いて
  Lb[:len(La)-1] == La[:-1]
が成り立つなら「梯子の古い段は同変、上 1 段だけが暫定」と言える。
"""
import sys
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, rows3L
from h10L3 import seg, L_at, diff
from core import expand, show

def run(lim=6, nmax=4):
    A=sorted(rows3.gen3('BMS',lim,zcap=1), key=rows3.key)
    c=Counter(); first=Counter(); ex={}
    for M in A:
        S=tuple(map(tuple,M)); sg=seg(S)
        if sg is None: continue
        r,bp,delta,t=sg
        for n in range(2,nmax+1):
            E=[tuple(x) for x in expand(S,n)]
            heads=[r+a*bp for a in range(n)]
            if heads[-1]>=len(E): continue
            out,rec=rows3L.b2d3L(list(E))
            rs=[L_at(rec,h) for h in heads]
            for a in range(n-1):
                x,y=rs[a],rs[a+1]
                if x is None or y is None: continue
                La,Lb=x['L'],y['L']
                d_all=diff(La,Lb,bp)
                d_cut=diff(La[:-1],Lb,bp) if La else None
                c[('全段一致' if d_all is None else '全段:×',
                   '上 1 段を除けば一致' if d_cut is None else '上 1 段を除いても×')]+=1
                if d_cut is not None:
                    first[d_cut[:2]]+=1
                    if d_cut[:2] not in [e[0][:2] for e in ex.values()] and len(ex)<5:
                        ex[len(ex)]=(d_cut,S,n,heads[a],heads[a+1],x,y,bp)
    return c,first,ex

if __name__=='__main__':
    lim=int(sys.argv[1]) if len(sys.argv)>1 else 6
    nm=int(sys.argv[2]) if len(sys.argv)>2 else 4
    c,first,ex=run(lim,nm)
    print('写しの隣り合う対 %d 組（lim=%d, n<=%d, 写し 0 も入れる）'%(sum(c.values()),lim,nm))
    for k in sorted(c,key=str): print('   %-46s %d'%(str(k),c[k]))
    print(); print('上 1 段を除いても残る書き換え:')
    for k,v in first.most_common(12): print('   %-40s %d'%(str(k),v))
    print()
    for i,(d,S,n,h1,h2,x,y,bp) in sorted(ex.items()):
        print('=== 例 %d  ずれ=%s'%(i,d))
        print('   もと %s   n=%d  bp=%d'%(show([list(z) for z in S]),n,bp))
        print('   写し頭 %d: L=%s d=%s'%(h1,x['L'],x['d']))
        print('   写し頭 %d: L=%s d=%s'%(h2,y['L'],y['d']))
