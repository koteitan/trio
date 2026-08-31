# -*- coding: utf-8 -*-
"""**(ANC) / (ROW2-DEN)。**

## ⚠ 主語

    `Sj = mTower Q d e n ++ block.take (j+1)`、`br = len(mTower ...)`（ブロックの根）
    錐の中(X, j)   :⟺ `le1 X 0 j`（＝ `trio.is_ancestor(X,1,0,j)`）
    ブロッカー(y)  :⟺ `br < y` ∧ `entry Sj 1 y <= entry Sj 1 br`
    行 2 の破れ(X, j) :⟺ `entry X 2 j > 0` ∧ `hasParent (X.take (j+1)) 2 j` が偽

## (ROW2-DEN) **教訓 27**: 分母を出してから 0 件を語る

    真の分母 ＝ `entry X 2 j = 1` **かつ錐の外**の列
    ⟹ ★ L3 の `not_le1_zero_of_row2_break`（破れる列は必ず錐の外）も**独立に検算**する

## (ANC) 行 2 の破れで、**的の `le1` 祖先（ブロックの中）にブロッカーがあるか**
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1, mTower
from r141 import block
from r169 import domT
from r201 import dOf, eOf
from r206 import hr0


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
                    # ---------- (ROW2-DEN) 消費側 Q ----------
                    for j in range(1, len(Q)):
                        if Q[j][2] == 0: continue
                        c['(DEN) Q: 行2>0 の列'] += 1
                        inc = trio.is_ancestor(Q, 1, 0, j)
                        brk = trio.parent(Q[:j+1], 2, j) is None
                        if not inc: c['(DEN) Q: **行2>0 かつ錐の外**'] += 1
                        if inc and brk: c['⛔ (DEN) Q: 錐の中なのに破れ'] += 1
                        if brk: c['(DEN) Q: 破れ'] += 1
                        if not inc and brk: c['(DEN) Q: 錐の外での破れ'] += 1
                    for n in NS:
                        S0 = [tuple(x) for x in mTower(Q, d, e, n)]
                        Bk = block(Q, d, e, n)
                        br = len(S0)
                        for j in range(1, len(Q)):
                            Sj = [tuple(x) for x in S0 + Bk[:j + 1]]
                            isb = lambda y: y > br and Sj[y][1] <= Sj[br][1]
                            lastx = len(Sj) - 1
                            p = trio.parent(Sj, srow(Sj, lastx), lastx)
                            if p is None or lastx - p < 2: continue
                            V = [tuple(x) for x in Sj[p:lastx]]
                            for jj in range(1, len(V)):
                                if V[jj][2] == 0: continue
                                c['(DEN) V: 行2>0 の列'] += 1
                                inc = trio.is_ancestor(V, 1, 0, jj)
                                brk = trio.parent(V[:jj+1], 2, jj) is None
                                if not inc: c['(DEN) V: **行2>0 かつ錐の外**'] += 1
                                if brk: c['(DEN) V: 破れ'] += 1
                                if inc and brk: c['⛔ (DEN) V: 錐の中なのに破れ'] += 1
                                if not inc and brk: c['(DEN) V: 錐の外での破れ'] += 1
                                if not brk: continue
                                # ---------- (ANC) ----------
                                b = p + jj
                                ancB = [y for y in range(br, b)
                                        if trio.is_ancestor(Sj, 1, y, b)]
                                ancV = [y for y in range(jj)
                                        if trio.is_ancestor(V, 1, y, jj)]
                                c['(ANC) 分母（行2の破れ）'] += 1
                                c[f'   ブロック内の le1 祖先の数 {min(len(ancB),3)}'] += 1
                                if any(isb(y) for y in ancB):
                                    c['⛔ **(ANC) 祖先にブロッカーがいる**'] += 1
                                    if len(ex) < 5:
                                        bl = [(y - br, Sj[y][1]) for y in ancB if isb(y)]
                                        ex.append((Q, d, e, n, j, b - br, bl,
                                                   Sj[br][1], len(ancV)))
                                else:
                                    c['★ (ANC) 祖先にブロッカーは無い'] += 1
    def pc(a, b): return f'{a} ({100*a/max(b,1):8.4f}%)'
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    for X in ('Q', 'V'):
        d1 = c[f'(DEN) {X}: 行2>0 の列']; d2 = c[f'(DEN) {X}: **行2>0 かつ錐の外**']
        print(f'  (ROW2-DEN) **{X}**: 行2>0 {d1}  **錐の外 {pc(d2, d1)}**  '
              f'破れ {c[f"(DEN) {X}: 破れ"]}  '
              f'⟹ **錐の外での破れ率 {pc(c[f"(DEN) {X}: 錐の外での破れ"], d2)}**  '
              f'⛔ 錐の中なのに破れ {c[f"⛔ (DEN) {X}: 錐の中なのに破れ"]}')
    da = c['(ANC) 分母（行2の破れ）']
    print(f'  ★★ (ANC) 分母（行2の破れ）{da}  '
          f'★ **祖先にブロッカーは無い** {pc(c["★ (ANC) 祖先にブロッカーは無い"], da)}  '
          f'⛔ **いる** {pc(c["⛔ **(ANC) 祖先にブロッカーがいる**"], da)}')
    print('      ブロック内の le1 祖先の数: '
          + '  '.join(f'{k[-1]}:{c[k]}' for k in sorted(c)
                      if k.startswith('   ブロック内')))
    for x in ex:
        print(f'      ⛔ (ANC) 例 Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} '
              f'的(ブロック内)={x[5]} ブロッカー(相対,行1)={x[6]} 根の行1={x[7]}')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2), '|R|=3 行1<3')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2), '★ |R|=4 行1<3')
    run(4, 4, (0,1,2,3), (0,1), (0,1,2), (1,2), '★★ |R|=4 行1<4')
