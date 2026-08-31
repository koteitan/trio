# -*- coding: utf-8 -*-
"""H10 (1): 展開の写しの境目を expand と同じ式で出し、そこでの L / F を比べる。"""
import sys
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, rows3L
from core import pim, show

def seg(S):
    """expand と同じ計算で (r, bp, delta, t) を返す。写しは r, r+bp, r+2bp, ..."""
    if not S: return None
    X=len(S); x=X-1; Y=len(S[0])
    if all(v==0 for v in S[x]): return None
    t=max(y for y in range(Y) if S[x][y]>0)
    P=pim(S); r=P[x][t]
    if r==-1: return None
    delta=[(S[x][y]-S[r][y]) if y<t else 0 for y in range(Y)]
    return r, x-r, tuple(delta), t

def L_at(rec, off):
    for R in rec:
        if R['off']==off: return R
    return None

def cmp_pair(a, b):
    """L_a と L_b を比べ、(判定, 最初にずれた成分) を返す。"""
    La, Lb = a['L'], b['L']
    if La==Lb: return 'L 一致', None
    if len(La)!=len(Lb): return 'L 長さがちがう', ('len', len(La), len(Lb))
    for k in range(len(La)):
        ea, eb = La[k], Lb[k]
        for j in range(min(len(ea),len(eb))):
            if ea[j]!=eb[j]:
                nm = ['深い側 row1','その row2','force1','浅い側 row1','sibL','src'][j]
                return 'L がちがう', (k, j, nm, ea[j], eb[j])
    return 'L がちがう', ('?',)

def run(lim=6, nmax=4):
    A=sorted(rows3.gen3('BMS',lim,zcap=1), key=rows3.key)
    c=Counter(); first=Counter(); ex={}
    for M in A:
        S=tuple(map(tuple,M)); sg=seg(S)
        if sg is None: continue
        r,bp,delta,t=sg
        for n in range(2,nmax+1):
            E=[tuple(x) for x in rows3.expand(S,n)] if hasattr(rows3,'expand') else None
            if E is None:
                from core import expand as _ex; E=[tuple(x) for x in _ex(S,n)]
            heads=[r+a*bp for a in range(n)]
            if heads[-1]>=len(E): continue
            out,rec=rows3L.b2d3L(list(E))
            rs=[L_at(rec,h) for h in heads]
            for a in range(n-1):
                x,y=rs[a],rs[a+1]
                if x is None or y is None:
                    c['写しの頭で conv3 が呼ばれない']+=1; continue
                vL,d=cmp_pair(x,y)
                vF='F 一致' if x['F']==y['F'] else 'F がちがう'
                c[(vL,vF)]+=1
                if d: first[(d[0],d[1],d[2]) if len(d)>2 and d[0]!='len' else d[:1]]+=1
                if vL!='L 一致' and len(ex)<4 and (d[:3] not in [e[0][:3] for e in ex.values()] if ex else True):
                    ex[len(ex)]=(d,S,n,heads[a],heads[a+1],x,y,delta,t)
    return c,first,ex

if __name__=='__main__':
    lim=int(sys.argv[1]) if len(sys.argv)>1 else 6
    nm=int(sys.argv[2]) if len(sys.argv)>2 else 4
    c,first,ex=run(lim,nm)
    print('写しの隣り合う対 %d 組（lim=%d, n<=%d）'%(sum(c.values()),lim,nm))
    for k in sorted(c,key=str): print('   %-38s %d'%(str(k),c[k]))
    print()
    print('最初にずれた成分:')
    for k,v in first.most_common(12): print('   %-44s %d'%(str(k),v))
    print()
    for i,(d,S,n,h1,h2,x,y,delta,t) in sorted(ex.items()):
        print('=== 例 %d  ずれ=%s'%(i,d))
        print('   もと %s   n=%d  delta=%s t=%d'%(show([list(z) for z in S]),n,delta,t))
        print('   写しの頭 %d: L=%s F=%s d=%s ps=%s'%(h1,x['L'],x['F'],x['d'],x['ps']))
        print('   写しの頭 %d: L=%s F=%s d=%s ps=%s'%(h2,y['L'],y['F'],y['d'],y['ps']))
