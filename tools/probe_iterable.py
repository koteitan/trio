# -*- coding: utf-8 -*-
"""`Iterable` の反証器（梯子が実際に作る形に絞る）。

    Iterable P := forall q < |P|, forall n,  P.take q ++ (P.drop q)^n  in W 0

`snoc_flat` は「末尾 1 列は、その親の位置での接尾辞コピー族が済んでいれば無料」
なので、`Iterable` が閉じれば梯子は全部回る。ここでは母集団を**梯子が生成する形**
に絞って反証を探す:

    X ++ (1,0,0)^a1 (2,0,0)^a2 ... (d,0,0)^ad     （降順の深さの塊）

上界は `r49.Wup`（False が健全）。False が出たら本物の反例。
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r49

X = [(0, 0, 0), (1, 1, 1)]

def s(m): return ''.join('(%d,%d,%d)' % c for c in m)

def ladder(exps):
    """exps = [a1, a2, ..., ad] -> X ++ (1,0,0)^a1 ... (d,0,0)^ad"""
    out = list(X)
    for d, a in enumerate(exps, start=1):
        out += [(d, 0, 0)] * a
    return out

def main(maxd=4, maxa=3, nmax=3, N=2, depth=7, maxlen=20):
    pats = []
    for d in range(1, maxd + 1):
        for exps in itertools.product(range(1, maxa + 1), repeat=d):
            P = ladder(list(exps))
            if len(P) <= maxlen: pats.append((exps, P))
    print('梯子の形: %d 本' % len(pats))
    tested = ce = 0
    for exps, P in pats:
        for q in range(1, len(P)):
            blk = P[q:]
            if not blk: continue
            for n in range(1, nmax + 1):
                M = P[:q] + blk * n
                if len(M) > maxlen: break
                tested += 1
                if r49.Wup(M, 0, depth, {}, N, maxlen) is False:
                    ce += 1
                    if ce <= 6:
                        print('★ 反例  P=%s  q=%d  n=%d\n        %s'
                              % (s(P), q, n, s(M)))
    print('判定 %d 件 / 反例 %d 件' % (tested, ce))

if __name__ == '__main__':
    main(*(int(a) for a in sys.argv[1:]))
