# -*- coding: utf-8 -*-
"""**(C4)(C5) —— 残差の形から作った候補。**

残差はつねに `V = [(x,a,0),(x+1,a,0)]`（**行 1 が等しい隣接 2 列**）。
⟹ ★ C1「行 1 = 0 の列が無い」では防げない。⟹ **行 1 の狭義増加**が要る。

    (C4) `∀ y < j, le0 Q y j → entry Q 1 y < entry Q 1 j`   `le0` に沿って行 1 が狭義増加
    (C5) `∀ i, 0 < i → entry Q 1 (i-1) < entry Q 1 i`       行 1 が左から狭義増加（より強い）
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1, mTower
from r141 import block
from r169 import domT
from r201 import dOf, eOf
from r206 import hr0
from r248 import hlocQ
from r255 import Dv, C1

C4 = lambda X: all(X[y][1] < X[j][1] for j in range(1, len(X)) for y in range(j)
                   if trio.is_ancestor(X, 0, y, j))
C5 = lambda X: all(X[i-1][1] < X[i][1] for i in range(1, len(X)))
CS = (('C1', C1), ('C4 le0 に沿って行1 が狭義増加', C4), ('C5 行1 が左から狭義増加', C5))


def run(L, R1, VS, ZS, TS, NS, tag):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    c = Counter(); ex = []; t0 = time.time()
    for Rt in itertools.product(COL, repeat=L):
        R = list(Rt)
        if srow(R, len(R) - 1) != 2: continue
        if not any(domT(R, m) for m in range(4)): continue
        for v in VS:
            for z in ZS:
                if trio.parent([(0, v, z)] + R, 2, len(R)) is None: continue
                for t in TS:
                    M = [tuple(x) for x in Lift1([(0, v, z)] + R, t)]
                    Q = M[:-1]
                    if len(Q) < 2: continue
                    d, e = dOf(M), eOf(M)
                    if not (d > 0 and hr0(Q) and Q[0][2] == 0): continue
                    hits = [(nm, f(Q)) for nm, f in CS]; hq = hlocQ(Q)
                    for n in NS:
                        S0 = [tuple(x) for x in mTower(Q, d, e, n)]
                        Bk = [tuple(x) for x in block(Q, d, e, n)]
                        br = len(S0)
                        for j in range(1, len(Q)):
                            Sj = S0 + Bk[:j + 1]
                            isb = lambda y: y > br and Sj[y][1] <= Sj[br][1]
                            lastx = len(Sj) - 1
                            p = trio.parent(Sj, srow(Sj, lastx), lastx)
                            if p is None or lastx - p < 2: continue
                            V = [tuple(x) for x in Sj[p:lastx]]
                            for (nm, ok), (_, f) in zip(hits, CS):
                                if not ok: continue
                                c[f'({nm}) 窓'] += 1
                                if f(V): c[f'★ ({nm}) (b) 遺伝'] += 1
                                if V[0][2] != 0: c[f'⛔ ({nm}) hz0(V) が偽'] += 1
                                for b in range(br, len(Sj)):
                                    if Sj[b][2] == 0: continue
                                    anc = [y for y in range(br, b)
                                           if trio.is_ancestor(Sj, 1, y, b)]
                                    if not anc: continue
                                    c[f'({nm}) 祖先 1 個以上'] += 1
                                    if any(isb(y) for y in anc):
                                        c[f'⛔ ({nm}) 祖先にブロッカー'] += 1
                                if not hq: continue
                                c[f'({nm}) 条件つき窓'] += 1
                                if hlocQ(V): c[f'★ ({nm}) hlocQ(V) 真'] += 1
                                else:
                                    c[f'⛔ ({nm}) **残差**'] += 1
                                    if nm.startswith('C5') and len(ex) < 3:
                                        ex.append((Q, d, e, n, j, V))
    def pc(a, b): return f'{a} ({100*a/max(b,1):8.4f}%)'
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    for nm, _ in CS:
        dw = c[f'({nm}) 窓']; da = c[f'({nm}) 祖先 1 個以上']; dc = c[f'({nm}) 条件つき窓']
        print(f'  **{nm}**: 窓 {dw}  ★ (b)遺伝 {pc(c[f"★ ({nm}) (b) 遺伝"], dw)}  '
              f'⛔ hz0(V) 偽 {pc(c[f"⛔ ({nm}) hz0(V) が偽"], dw)}')
        print(f'        祖先1個以上 {da} ⛔ **うちブロッカー** '
              f'{pc(c[f"⛔ ({nm}) 祖先にブロッカー"], da)}   '
              f'条件つき窓 {dc} ★ **hlocQ(V) 真** {pc(c[f"★ ({nm}) hlocQ(V) 真"], dc)} '
              f'⛔ **残差** {c[f"⛔ ({nm}) **残差**"]}')
    for x in ex:
        print(f'      ⛔ C5 真なのに残差: Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} V={x[5]}')
    print()


if __name__ == '__main__':
    print('## (a) 中核 D_v')
    for v in range(1, 8):
        print(f'   D_{v}: ' + '  '.join(f'{nm}={"★真" if f(Dv(v)) else "⛔偽"}'
                                        for nm, f in CS))
    print()
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2), '★ |R|=4 行1<3')
    run(4, 4, (0,1,2,3), (0,1), (0,1,2), (1,2), '★★ |R|=4 行1<4')
    run(5, 3, (0,1,2), (0,1), (0,1), (1,2), '★★ |R|=5 行1<3')
