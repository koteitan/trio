# -*- coding: utf-8 -*-
"""**(C1) の (c) ＋ 箱の伸ばし。**

    (C1) `∀ i, 0 < i → 0 < entry Q 1 i`   行 1 = 0 の列が無い
    ⟹ ★ (a) 中核 `D_v` で真、(b) 遺伝 100% を通過済み（§R235）
    ⟹ ★★ (c) **(ROW2') の破れ / (ANC) の破れ / `hlocQ` の残差**が消えるか
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
from r255 import C1


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
                    c1 = C1(Q); hq = hlocQ(Q)
                    for n in NS:
                        S0 = [tuple(x) for x in mTower(Q, d, e, n)]
                        Bk = [tuple(x) for x in block(Q, d, e, n)]
                        br = len(S0)
                        for j in range(1, len(Q)):
                            Sj = S0 + Bk[:j + 1]
                            isb = lambda y: y > br and Sj[y][1] <= Sj[br][1]
                            tg = 'C1真' if c1 else 'C1偽'
                            # ---------- (ROW2') / (ANC) ----------
                            for b in range(br, len(Sj)):
                                if Sj[b][2] == 0: continue
                                anc = [y for y in range(br, b)
                                       if trio.is_ancestor(Sj, 1, y, b)]
                                c[f'({tg}) ROW2 分母'] += 1
                                if not any(isb(y) for y in anc):
                                    c[f'★ ({tg}) 祖先が全部非ブロッカー'] += 1
                                if anc:
                                    c[f'({tg}) 祖先が 1 個以上'] += 1
                                    if any(isb(y) for y in anc):
                                        c[f'⛔ ({tg}) **祖先にブロッカー**'] += 1
                            # ---------- hlocQ ----------
                            lastx = len(Sj) - 1
                            p = trio.parent(Sj, srow(Sj, lastx), lastx)
                            if p is None or lastx - p < 2: continue
                            V = [tuple(x) for x in Sj[p:lastx]]
                            c[f'({tg}) C1(V)'] += 1 if C1(V) else 0
                            c[f'({tg}) 窓'] += 1
                            if V[0][2] != 0: c[f'⛔ ({tg}) hz0(V) が偽'] += 1
                            if not hq: continue
                            c[f'({tg}) 条件つき窓'] += 1
                            if hlocQ(V): c[f'★ ({tg}) hlocQ(V) が真'] += 1
                            else:
                                c[f'⛔ ({tg}) **残差**'] += 1
                                if c1 and len(ex) < 4:
                                    ex.append((Q, d, e, n, j, V))
    def pc(a, b): return f'{a} ({100*a/max(b,1):8.4f}%)'
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    for tg in ('C1真', 'C1偽'):
        d1 = c[f'({tg}) ROW2 分母']; d2 = c[f'({tg}) 祖先が 1 個以上']
        d3 = c[f'({tg}) 条件つき窓']; d4 = c[f'({tg}) 窓']
        print(f'  **{tg}**: ROW2 分母 {d1}  ★ 祖先が全部非ブロッカー '
              f'{pc(c[f"★ ({tg}) 祖先が全部非ブロッカー"], d1)}')
        print(f'          祖先 1 個以上 {d2}  ⛔ **うちブロッカー** '
              f'{pc(c[f"⛔ ({tg}) **祖先にブロッカー**"], d2)}')
        print(f'          窓 {d4}  ⛔ hz0(V) が偽 {pc(c[f"⛔ ({tg}) hz0(V) が偽"], d4)}  '
              f'★ C1(V) {pc(c[f"({tg}) C1(V)"], d4)}')
        print(f'          条件つき窓 {d3}  ★ **hlocQ(V) が真** '
              f'{pc(c[f"★ ({tg}) hlocQ(V) が真"], d3)}  ⛔ **残差** {c[f"⛔ ({tg}) **残差**"]}')
    for x in ex:
        print(f'      ⛔ C1真なのに残差: Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} V={x[5]}')
    print()


if __name__ == '__main__':
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2), '★ |R|=4 行1<3')
    run(4, 4, (0,1,2,3), (0,1), (0,1,2), (1,2), '★★ |R|=4 行1<4')
    run(5, 3, (0,1,2), (0,1), (0,1), (1,2), '★★ |R|=5 行1<3')
