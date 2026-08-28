# -*- coding: utf-8 -*-
"""H17b: `conv3(A)` の**末尾を差し替えた**候補を全数で試す（H3 の 81 通りの一般化）。

候補 D = conv3(A)[:k] ++ tail   （k = len-3 .. len-1、tail は 0..3 列）
条件: DBMS 標準形 / BMS 順の隣の像に挟まれる / ImgCofinalT が立つ
"""
import sys, time
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import rows3, cofinal
from core import expand, show, isstd
from rows3 import gen3, key, cmpmat

G = [((0, 0, 0), (1, 1, 1), (2, 0, 0), (3, 1, 1), (3, 1, 0), (1, 1, 1)),
     ((0, 0, 0), (1, 1, 1), (2, 0, 0), (3, 1, 1), (3, 1, 0), (4, 2, 0)),
     ((0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 0, 0), (3, 1, 1), (3, 1, 0)),
     ((0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 0, 0), (4, 1, 1), (4, 1, 0))]
B7 = sorted((tuple(map(tuple, M)) for M in gen3('BMS', 7, zcap=1)), key=key)


def tails(PRE, maxlen=3, maxa=12):
    out = []

    def rec(t):
        if t:
            out.append(tuple(t))
        if len(t) >= maxlen:
            return
        last = (PRE + tuple(t))[-1][0] if (PRE or t) else 0
        for a in range(0, min(last + 2, maxa) + 1):
            for b in range(0, a + 1):
                for c in range(0, min(b, 1) + 1):
                    if isstd(PRE + tuple(t) + ((a, b, c),), 'DBMS'):
                        rec(t + [(a, b, c)])
    rec([])
    return out


for A in G:
    fA = tuple(map(tuple, rows3.b2d3(list(A))))
    lo = hi = None
    for M in B7:
        if cmpmat(M, A) < 0:
            lo = M
        if cmpmat(A, M) < 0:
            hi = M
            break
    flo = tuple(map(tuple, rows3.b2d3(list(lo)))) if lo else None
    fhi = tuple(map(tuple, rows3.b2d3(list(hi)))) if hi else None
    cand = set()
    for k in range(max(1, len(fA) - 3), len(fA)):
        PRE = fA[:k]
        if not isstd(PRE, 'DBMS'):
            continue
        cand.add(PRE)
        for t in tails(PRE):
            cand.add(PRE + t)
    win = [D for D in sorted(cand, key=key)
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
    print('   候補 %d 個 -> 順序の窓に入る %d 個 -> **ImgCofinalT が立つ %d 個**'
          % (len(cand), len(win), len(ok)))
    print('   （いまの像は窓に入っているか: %s）' % (fA in win))
    for D, pat in ok[:5]:
        print('      **%s**  %s' % (show([list(x) for x in D]), pat))
