# -*- coding: utf-8 -*-
"""H10 (1c): 書き換えは「最初の写しだけが特別」なのか、写しの番号 a ごとに数える。"""
import sys
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
import rows3, rows3L
from h10L3 import seg, L_at, diff
from core import expand

def run(lim=5, nmax=6):
    A=sorted(rows3.gen3('BMS',lim,zcap=1), key=rows3.key)
    per=Counter(); tot=Counter(); kind=Counter()
    for M in A:
        S=tuple(map(tuple,M)); sg=seg(S)
        if sg is None: continue
        r,bp,delta,t=sg
        E=[tuple(x) for x in expand(S,nmax)]
        heads=[r+a*bp for a in range(nmax)]
        if heads[-1]>=len(E): continue
        out,rec=rows3L.b2d3L(list(E))
        rs=[L_at(rec,h) for h in heads]
        for a in range(nmax-1):
            x,y=rs[a],rs[a+1]
            if x is None or y is None: continue
            tot[a]+=1
            d=diff(x['L'], y['L'], bp)
            if d is not None:
                per[a]+=1; kind[(a,d[:2])]+=1
    return per,tot,kind

if __name__=='__main__':
    lim=int(sys.argv[1]) if len(sys.argv)>1 else 5
    nm=int(sys.argv[2]) if len(sys.argv)>2 else 6
    per,tot,kind=run(lim,nm)
    print('写しの番号 a -> a+1 ごとの「前の段の書き換え」（lim=%d, n=%d）'%(lim,nm))
    for a in sorted(tot):
        print('   写し %d -> %d : 書き換え %4d / %4d  (%.1f%%)'
              %(a,a+1,per[a],tot[a],100.0*per[a]/max(tot[a],1)))
    print()
    print('中身（上位）:')
    for k,v in kind.most_common(14): print('   %-42s %d'%(str(k),v))
