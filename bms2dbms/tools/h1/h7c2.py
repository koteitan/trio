# -*- coding: utf-8 -*-
"""tt が壊す C2 の 3 本を特定して、どの柱がどうずれたかを出す。"""
import sys, time
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, rows3m
from core import expand, show
from rows3 import cmpmat, key

def c2bad(f, A, mc=40, nn=24):
    bad=[]
    for M in A:
        if len(M)<2: continue
        N=tuple(map(tuple,f(list(M))))
        E=[tuple(expand(N,m)) for m in range(1,mc+1)]
        Mt=tuple(map(tuple,M))
        for n in range(1,nn+1):
            g=tuple(f([tuple(c) for c in expand(Mt,n)]))
            if not any(cmpmat(g,e)<=0 for e in E):
                bad.append((Mt,n,N,g)); break
    return bad

if __name__ == '__main__':
    lim=int(sys.argv[1]) if len(sys.argv)>1 else 6
    A=sorted(rows3.gen3('BMS',lim,zcap=1), key=key)
    res={}
    for combo in ((), ('tt',)):
        for k in rows3m.MX: rows3m.MX[k]=(k in combo)
        t=time.time(); b=c2bad(rows3m.b2d3, A)
        res[combo]=b
        print('%-6s C2 の破れ %d 個  %.0fs' % (','.join(combo) or 'なし', len(b), time.time()-t), flush=True)
    base={x[0] for x in res[()]}
    new=[x for x in res[('tt',)] if x[0] not in base]
    print()
    print('tt で新しく壊れた %d 個:' % len(new))
    for Mt,n,N,g in new:
        print('   A = %s   n=%d' % (show([list(c) for c in Mt]), n))
        print('      f(A)    = %s' % show([list(c) for c in N]))
        print('      f(A<n>) = %s' % show([list(c) for c in g]))
        for m in (n-1,n,n+1):
            if m<1: continue
            print('      f(A)<%d> = %s' % (m, show([list(c) for c in expand(N,m)])))
