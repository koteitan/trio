# -*- coding: utf-8 -*-
"""H10 (1b): 梯子は「伸びるだけ」か（前の段を書き換えないか）。

写し a の頭の L を La、写し a+1 の頭の L を Lb とする。同変なら
  Lb[:len(La)] は La と（src を写しの長さ bp だけずらして）一致するはず。
最初にずれた (段, 成分) を数える。
"""
import sys
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, rows3L
from core import pim, show, expand

NM=['深い側 row1','その row2','force1','浅い側 row1','sibL','src']

def seg(S):
    if not S: return None
    X=len(S); x=X-1; Y=len(S[0])
    if all(v==0 for v in S[x]): return None
    t=max(y for y in range(Y) if S[x][y]>0)
    P=pim(S); r=P[x][t]
    if r==-1: return None
    return r, x-r, tuple((S[x][y]-S[r][y]) if y<t else 0 for y in range(Y)), t

def L_at(rec, off):
    for R in rec:
        if R['off']==off: return R
    return None

def diff(La, Lb, bp):
    """Lb の前半が La と合うか。合わない最初の (段, 成分) を返す。"""
    if len(Lb) < len(La): return ('前の段が減った', len(La), len(Lb))
    for k in range(len(La)):
        ea, eb = La[k], Lb[k]
        if len(ea)!=len(eb): return (k,'長さ',len(ea),len(eb))
        for j in range(len(ea)):
            if ea[j]==eb[j]: continue
            if j==5 and ea[j] is not None and eb[j] is not None and eb[j]-ea[j]==bp:
                continue                      # src はもとの添字。写しの長さだけずれるのが正しい
            return (k, NM[j], ea[j], eb[j])
    return None

def run(lim=6, nmax=4, skip0=True):
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
            a0 = 1 if skip0 else 0
            for a in range(a0, n-1):
                x,y=rs[a],rs[a+1]
                if x is None or y is None:
                    c['写しの頭で conv3 が呼ばれない']+=1; continue
                dL=diff(x['L'], y['L'], bp)
                dF=diff(tuple((f,) for f in x['F']), tuple((f,) for f in y['F']), bp)
                c[('梯子は伸びるだけ' if dL is None else '**前の段を書き換えた**',
                   'F も伸びるだけ' if dF is None else '**F を書き換えた**')]+=1
                if dL is not None:
                    first[dL[:2]]+=1
                    if dL[:2] not in [e[0][:2] for e in ex.values()] and len(ex)<5:
                        ex[len(ex)]=(dL,S,n,heads[a],heads[a+1],x,y,bp)
    return c,first,ex

if __name__=='__main__':
    lim=int(sys.argv[1]) if len(sys.argv)>1 else 6
    nm=int(sys.argv[2]) if len(sys.argv)>2 else 4
    sk=len(sys.argv)<4 or sys.argv[3]!='all'
    c,first,ex=run(lim,nm,sk)
    print('写しの隣り合う対 %d 組（lim=%d, n<=%d, 写し 0 を%s）'
          %(sum(c.values()),lim,nm,'外す' if sk else '入れる'))
    for k in sorted(c,key=str): print('   %-44s %d'%(str(k),c[k]))
    print(); print('最初に書き換えた (段, 成分):')
    for k,v in first.most_common(12): print('   %-40s %d'%(str(k),v))
    print()
    for i,(d,S,n,h1,h2,x,y,bp) in sorted(ex.items()):
        print('=== 例 %d  ずれ=%s'%(i,d))
        print('   もと %s   n=%d  bp=%d'%(show([list(z) for z in S]),n,bp))
        print('   写し頭 %d: L=%s F=%s d=%s'%(h1,x['L'],x['F'],x['d']))
        print('   写し頭 %d: L=%s F=%s d=%s'%(h2,y['L'],y['F'],y['d']))
