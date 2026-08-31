# -*- coding: utf-8 -*-
"""**課題 (s7) —— 帰納の**実際の** `A'` で親の位置と測度を測る。**

## 母集団の作り方（厳密に。教訓「分母には作り方も書く」）

    `Q` … 消費側（`Lift1 ((0,v,z) :: R.dropLast) t`）。`TowerP''`（`0<|Q|` / `hr0` / `hz0`）＋ `d>0`
    `A0` … 空 ／ 1 列 ／ **人工的に浅い 1 列（陰性対照 (s7d)）**
    深さ 1: `P := A0 ++ mTower Q d e n`、`B := Lift1 (shiftr01 (d*n) 0 Q) (e*n)`
            親が `P.length + p`（`p < j`）⟹ `A' := P ++ B.take p`、`V := 窓`、`(d0,e0)` は `oper`
    深さ 2: `A' ++ mTower V d0 e0 m ++ B'.take (j'+1)` の**末尾列の親**を分類

## 分類（深さ 2 の対象に対して）

    **(A) 新しいブロック `B'` の中**
    **(B) `mTower V d0 e0 m` の最後のブロック（1 ブロック手前）**
    **⛔ (C) それより前の塔の部分**
    **⛔ (D) `A'` の中**

## ★ 予想（教訓 45）

> **⚠ §R210 で **`rsum A' V` は常に破れる**（0 / 1,162,245）。**
> **⚠ (s5) では `rsum` が破れると (D) が 83% 出た。⟹ **ここでも (D) が出る**と予想。見積もり 20〜80%。**
> **⚠ (s7b) `|V'| <= |V|` も破れると予想。**
> **⚠ 外れて (C)(D) が 0 なら、**帰納の `A'` は人工的な浅い `A` と違う**ことになる（大きい）。**
"""
import sys, itertools, random, time
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


def run(L, R1, VS, ZS, TS, NS, MS, tag, seed):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    rnd = random.Random(seed); c = Counter(); ex = []; t0 = time.time()
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
                    LQ = len(Q)
                    for a0name, A0 in (('A0 空', []),
                                       ('A0 1 列', [(rnd.randrange(5), rnd.randrange(5),
                                                   rnd.randrange(2))]),
                                       ('★ (s7d) A0 人工的に浅い', [(0, 0, 0)])):
                        for n in NS:
                            T = [tuple(x) for x in mTower(Q, d, e, n)]
                            P = A0 + T
                            B = block(Q, d, e, n)
                            for j in range(1, LQ):
                                S1 = P + B[:j + 1]
                                last1 = len(S1) - 1
                                par1 = trio.parent(S1, srow(S1, last1), last1)
                                if par1 is None or par1 < len(P): continue
                                p = par1 - len(P)
                                if p >= j: continue
                                A2 = P + B[:p]                 # ★ 実際の A'
                                V = [tuple(x) for x in S1[par1:last1]]
                                if len(V) < 2: continue
                                i1 = srow(S1, last1)
                                d0 = (S1[last1][0] - S1[par1][0]) if i1 > 0 else 0
                                e0 = (S1[last1][1] - S1[par1][1]) if i1 > 1 else 0
                                LV = len(V)
                                for m in MS:
                                    T2 = [tuple(x) for x in mTower(V, d0, e0, m)]
                                    B2 = block(V, d0, e0, m)
                                    for j2 in range(LV):
                                        S2 = A2 + T2 + B2[:j2 + 1]
                                        lastX = len(S2) - 1
                                        par2 = trio.parent(S2, srow(S2, lastX), lastX)
                                        c[(a0name, '★ 分母: 深さ 2 の段')] += 1
                                        if par2 is None:
                                            c[(a0name, '親なし（孤児）')] += 1
                                            continue
                                        nA2 = len(A2)
                                        if par2 < nA2:
                                            w = '⛔ (D) A\' の中'
                                            if par2 < len(A0): w += '（うち A0 の中）'
                                        elif par2 >= nA2 + len(T2):
                                            w = '(A) 新しいブロックの中'
                                        else:
                                            k = (par2 - nA2) // LV
                                            w = ('(B) 1 ブロック手前' if k == m - 1
                                                 else '⛔ (C) 2 ブロック以上手前')
                                        c[(a0name, w)] += 1
                                        Vp = lastX - par2
                                        c[(a0name, ('★ |V\'| <= |V|' if Vp <= LV
                                                    else '⛔ |V\'| > |V|'))] += 1
                                        if w.startswith('⛔') and len(ex) < 4:
                                            ex.append((a0name, Q, d, e, n, j, p, V, d0, e0,
                                                       m, j2, par2, nA2, w))
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    for a0name in ('A0 空', 'A0 1 列', '★ (s7d) A0 人工的に浅い'):
        D = c[(a0name, '★ 分母: 深さ 2 の段')]
        if not D: continue
        print(f'  {a0name}   ★ 分母（深さ 2 の段）{D}')
        for w in ['親なし（孤児）', '(A) 新しいブロックの中', '(B) 1 ブロック手前',
                  '⛔ (C) 2 ブロック以上手前', "⛔ (D) A' の中", "⛔ (D) A' の中（うち A0 の中）",
                  "★ |V'| <= |V|", "⛔ |V'| > |V|"]:
            if c[(a0name, w)] or w.startswith(('(A)', '(B)', '⛔', '★')):
                print(f'      {w:34s} {c[(a0name,w)]:9d} ({100*c[(a0name,w)]/D:8.4f}%)')
    for x in ex:
        print(f'      ⛔ 例 [{x[0]}] Q={x[1]} d={x[2]} e={x[3]} n={x[4]} j={x[5]} p={x[6]} '
              f'V={x[7]} (d0,e0)=({x[8]},{x[9]}) m={x[10]} j2={x[11]} 親={x[12]} '
              f'|A\'|={x[13]} → {x[14]}')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), (1,2,3), '消費側 |R|=3 行1<3', 931)
    run(3, 5, (0,1,2), (0,1), (0,1,2), (1,2), (1,2,3), '★ 消費側 |R|=3 行1<5', 933)
