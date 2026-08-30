# -*- coding: utf-8 -*-
"""**(ROW2') / (RES)。**

## ⚠ 主語（どの列の中で何を見たか）

    `Sj  = mTower Q d e n ++ block.take (j+1)`      ← **`le1` はこの列の中で見る**
    `br  = len(mTower ...)`                          ← **ブロックの根の番地**
    ブロッカー(y) :⟺ `y != br` ∧ `y >= br` ∧ `entry Sj 1 y <= entry Sj 1 br`
      （H12 の `blocker_out_of_cone` の逐語: 根でなく、行 1 が根以下）

## (ROW2') 行 2 の的について

    **(A)** 的 `b` の `le1` 祖先のうち**ブロック内**のものが**全部非ブロッカー**か   ← H12 の案
    **(B)** ブロックの**全列**が非ブロッカーか（＝ `hnb` の ∀）                    ← 従来
    ⟹ ★ **(A) >> (B) なら ∀ が縮んだ甲斐があります**

## (RES) 条件つき残差

    `hlocQ(Q)` 真かつ `hlocQ(V)` 偽の窓を **行 1 の破れ / 行 2 の破れ**で分け、
    親の位置（**ブロックの中 / 塔の中**）を出す。
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
from r247 import row1_wit
from r248 import hlocQ


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
                    hq = hlocQ(Q)
                    for n in NS:
                        S0 = [tuple(x) for x in mTower(Q, d, e, n)]
                        Bk = block(Q, d, e, n)
                        br = len(S0)
                        for j in range(1, len(Q)):
                            Sj = [tuple(x) for x in S0 + Bk[:j + 1]]
                            blk = range(br, len(Sj))
                            isblk = lambda y: y != br and Sj[y][1] <= Sj[br][1]
                            hnb_all = not any(isblk(y) for y in blk)
                            # ============ (ROW2') 行 2 の的 ============
                            for b in blk:
                                if Sj[b][2] == 0: continue
                                c['(ROW2\') 行 2 の的 分母'] += 1
                                anc = [y for y in blk if y < b
                                       and trio.is_ancestor(Sj, 1, y, b)]
                                okA = not any(isblk(y) for y in anc)
                                if okA: c['★ (A) 的の le1 祖先が全部非ブロッカー'] += 1
                                else:
                                    c['⛔ (A) 祖先にブロッカーがいる'] += 1
                                    if len(ex) < 5:
                                        bl = [y for y in anc if isblk(y)]
                                        ex.append(('A', Q, d, e, n, j, br, b,
                                                   [(y - br, Sj[y][1]) for y in bl],
                                                   Sj[br][1]))
                                if hnb_all: c['★ (B) ブロック全列が非ブロッカー'] += 1
                                c[f'   祖先の数 {min(len(anc),4)}'] += 1
                            # ============ (RES) 条件つき残差 ============
                            lastx = len(Sj) - 1
                            p = trio.parent(Sj, srow(Sj, lastx), lastx)
                            if p is None or lastx - p < 2: continue
                            V = [tuple(x) for x in Sj[p:lastx]]
                            if not hq or hlocQ(V): continue
                            c['(RES) 残差'] += 1
                            for jj in range(1, len(V)):
                                if V[jj][2] > 0:
                                    if trio.parent(V[:jj+1], 2, jj) is not None: continue
                                    kind = '行 2 の破れ'
                                elif V[jj][1] > 0 and not row1_wit(V, jj):
                                    kind = '行 1 の破れ'
                                else: continue
                                c[f'★ (RES-a) {kind}'] += 1
                                jab = p + jj
                                pp = trio.parent(Sj[:jab+1], srow(Sj, jab), jab)
                                loc = ('孤児' if pp is None else
                                       ('ブロックの中' if pp >= br else '塔の中'))
                                c[f'  (RES-b) {kind} の親: {loc}'] += 1
                                if pp is not None:
                                    c[f'  (RES-b) {kind} の親の srow='
                                      f'{srow(Sj, jab)}'] += 1
    def pc(a, b): return f'{a} ({100*a/max(b,1):8.4f}%)'
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    dn = c["(ROW2') 行 2 の的 分母"]
    print(f'  ★★ (ROW2\') 行 2 の的 分母 {dn}')
    print(f'      ★ **(A) 的の le1 祖先が全部非ブロッカー** '
          f'{pc(c["★ (A) 的の le1 祖先が全部非ブロッカー"], dn)}   '
          f'⛔ 祖先にブロッカー {c["⛔ (A) 祖先にブロッカーがいる"]}')
    print(f'      （B) ブロック全列が非ブロッカー（従来の ∀） '
          f'{pc(c["★ (B) ブロック全列が非ブロッカー"], dn)}')
    print('      祖先の数: ' + '  '.join(f'{k[-1]}:{c[k]}' for k in sorted(c)
                                          if k.startswith('   祖先の数')))
    print(f'  ★ (RES) 残差 {c["(RES) 残差"]}')
    for k in sorted(c):
        if k.startswith('★ (RES-a)') or k.startswith('  (RES-b)'):
            print(f'      {k}: {c[k]}')
    for x in ex:
        print(f'      ⛔ (A) 例 Q={x[1]} d={x[2]} e={x[3]} n={x[4]} j={x[5]} '
              f'的(ブロック内)={x[7]-x[6]} ブロッカー(相対,行1)={x[8]} 根の行1={x[9]}')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2), '|R|=3 行1<3')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2), '★ |R|=4 行1<3')
