# -*- coding: utf-8 -*-
"""梯子が要求する形は、結局これ 1 本に集まる:

    P in W 0,  Deep P（根が深さ 0・他は深さ 1 以上）,
    Q != [],  Q の根が深さ 1,  Q の全列が深さ 1 以上
      ==>  P ++ Q^n in W 0

`Mm`（Q = (1,0,0)）/ `Rep`（Q = (1,0,0)(2,0,0)）/ `app_iter`（Q = App k）は
どれもこの特殊ケース。深さ 2 以上の梯子を辿ると、必ずこの形に戻ってくる。

下界（True が健全）: 緑の定理のみ  上界（False が健全）: r49.Wup
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r49

def lev(c): return 2 * c[1] + c[2]
def s(m): return ''.join('(%d,%d,%d)' % c for c in m)

def certified(M, u):
    if not M: return True
    if lev(M[0]) > u: return False
    if all(c[2] == 0 for c in M): return True
    if len(M) == 2 and M[0][0] == 0: return True
    return r49.Wlo(M)

def deep(P):
    return P and P[0][0] == 0 and all(c[0] >= 1 for c in P[1:])

def main(maxP=4, maxQ=3, maxval=3, nmax=3, N=2, depth=7, maxlen=18):
    cols = [(x, y, z) for x in range(maxval + 1) for y in range(maxval + 1) for z in (0, 1)]
    Ps = []
    for k in range(1, maxP + 1):
        for tail in itertools.product(cols, repeat=k - 1):
            P = ((0, 0, 0),) + tail
            if deep(P) and certified(P, 0): Ps.append(P)
    Qs = []
    for k in range(1, maxQ + 1):
        for Q in itertools.product([c for c in cols if c[0] >= 1], repeat=k):
            if Q[0][0] == 1: Qs.append(Q)
    print('Deep かつ certified な P: %d 本 /  深さ 1 に根を持つ Q: %d 本' % (len(Ps), len(Qs)))
    tested = ce = 0
    for P in Ps:
        for Q in Qs:
            for n in range(1, nmax + 1):
                M = list(P) + list(Q) * n
                if len(M) > maxlen: break
                tested += 1
                if r49.Wup(M, 0, depth, {}, N, maxlen) is False:
                    ce += 1
                    if ce <= 6:
                        print('★ 反例  P=%s  Q=%s  n=%d\n        %s' % (s(P), s(Q), n, s(M)))
    print('判定 %d 件 / 反例 %d 件' % (tested, ce))

if __name__ == '__main__':
    main(*(int(a) for a in sys.argv[1:]))
