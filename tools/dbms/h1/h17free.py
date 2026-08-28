# -*- coding: utf-8 -*-
"""H17: シートに載っていない γ 4 個で、`conv3(A)` を綴り直せば ImgCofinalT が立つか。

`conv3` は BMS 標準形の順序を保つので、`A` の**BMS 順の隣**の像が `D` を挟む。
その窓の中の DBMS 標準形を全数で試す。
"""
import sys, time
from collections import Counter
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import rows3, inv3, cofinal
from core import expand, show, isstd
from rows3 import gen3, key, cmpmat

G = [((0, 0, 0), (1, 1, 1), (2, 0, 0), (3, 1, 1), (3, 1, 0), (1, 1, 1)),
     ((0, 0, 0), (1, 1, 1), (2, 0, 0), (3, 1, 1), (3, 1, 0), (4, 2, 0)),
     ((0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 0, 0), (3, 1, 1), (3, 1, 0)),
     ((0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 0, 0), (4, 1, 1), (4, 1, 0))]
B7 = sorted((tuple(map(tuple, M)) for M in gen3('BMS', 7, zcap=1)), key=key)
D8 = sorted((tuple(map(tuple, M)) for M in gen3('DBMS', 8, zcap=1)), key=key)
print('BMS 標準形 <=7 列 %d / DBMS 標準形 <=8 列 %d' % (len(B7), len(D8)))
for A in G:
    fA = tuple(map(tuple, rows3.b2d3(list(A))))
    # BMS 順の隣
    lo = hi = None
    for M in B7:
        if cmpmat(M, A) < 0:
            lo = M
        if cmpmat(A, M) < 0:
            hi = M
            break
    flo = tuple(map(tuple, rows3.b2d3(list(lo)))) if lo else None
    fhi = tuple(map(tuple, rows3.b2d3(list(hi)))) if hi else None
    win = [D for D in D8
           if (flo is None or cmpmat(flo, D) < 0)
           and (fhi is None or cmpmat(D, fhi) < 0)]
    ok = []
    for D in win:
        pat = cofinal.hits(A, 8, f=lambda X: list(D)
                           if tuple(map(tuple, X)) == A else rows3.b2d3(X))
        if pat[-3:] == 'OOO':
            ok.append((D, pat))
    print()
    print('A = %s' % show(list(A)))
    print('   いまの像 = %s' % show([list(x) for x in fA]))
    print('   BMS 順の隣: %s / %s' % (show(list(lo)) if lo else None,
                                      show(list(hi)) if hi else None))
    print('   窓の中の DBMS 標準形 %d 個 -> **ImgCofinalT が立つもの %d 個**'
          % (len(win), len(ok)))
    for D, pat in ok[:5]:
        print('      %s  %s' % (show([list(x) for x in D]), pat))
