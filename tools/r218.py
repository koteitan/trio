# -*- coding: utf-8 -*-
"""**課題 (x1) —— `OrphOK`: ブロック内の孤児は、塔を前に付けても孤児か。**

## 的（team-lead が L3 から渡した形）

    ブロック `B := Lift1 (shiftr01 (d*n) 0 Q) (e*n)` の中で列 `j` が孤児
      （＝ `¬ hasParent (B.take (j+1)) (srow (B.take (j+1)) j) j`）
    ⟹ **`A ++ mTower Q d e n ++ B.take (j+1)` の中でも孤児**

## ⚠ 判定できる範囲（明記）

`A ∈ W u` は**判定しない**（規則）。⟹ 2 段階で測る:

    **(x1a) `A = []`**（＝ 塔だけを前に付ける）… **完全に判定できる**
    **(x1b) `A` にランダムな列を付ける**… ⚠ **`A ∈ W u` は判定していない上位集合**

## ★ 予想（教訓 45）＋ 見積もり

> **⚠ 塔を前に付けると**行 0 の小さい列**が増える（`d > 0` なら前のブロックほど行 0 が小さい）
>   ⟹ **親が生まれうる**。⟹ **100% にならない**と予想。見積もり **30〜70%**。**
> **⚠ 反例が出たら、列と**親の位置（何ブロック手前か）**をそのまま貼る。**

## 分母

**`TowerP''(Q)` の 5 本**（`0<|Q|` / `0<d` / `0<e` / `hr0` / `hz0`）を満たす消費側の `Q`。
そこから作った塔とブロックで、**ブロック内で孤児な列**（件数を出す）。
"""
import sys, itertools, random, time
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


def orphan(S, j):
    return trio.parent(S, srow(S, j), j) is None


def run(L, R1, VS, ZS, TS, NS, seed, ALEN):
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
                    # TowerP'' の 5 本
                    if not (len(Q) >= 1 and d > 0 and e > 0 and hr0(Q) and Q[0][2] == 0):
                        continue
                    c['Q 側の分母（5 本）'] += 1
                    for n in NS:
                        B = block(Q, d, e, n)
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        for j in range(len(Q)):
                            Bt = B[:j + 1]
                            c['ブロック内の列'] += 1
                            if not orphan(Bt, j): continue
                            jk = 'j=0' if j == 0 else 'j>=1'
                            c['★ 分母: ブロック内で孤児な列'] += 1
                            c[(jk, '分母')] += 1
                            c[('孤児の srow', srow(Bt, j))] += 1
                            # (x1a) A = []
                            S = T + Bt
                            idx = len(T) + j
                            if orphan(S, idx):
                                c['★ (x1a) 塔を付けても孤児'] += 1
                                c[(jk, '★ 孤児のまま')] += 1
                            else:
                                c[(jk, '⛔ 親ができる')] += 1
                                c['⛔ (x1a) 塔を付けると親ができる'] += 1
                                par = trio.parent(S, srow(S, idx), idx)
                                blk = par // len(Q) if par < len(T) else 'ブロック内'
                                c[('⛔ 親のブロック（手前へ何個）',
                                   (len(T)//len(Q)) - blk if isinstance(blk, int) else -1)] += 1
                                if len(ex) < 4:
                                    ex.append((Q, d, e, n, j, srow(Bt, j), par, blk, S))
                            # (x1b) ランダムな A（⚠ W 所属は判定していない）
                            A = [(rnd.randrange(6), rnd.randrange(6), rnd.randrange(2))
                                 for _ in range(ALEN)]
                            S2 = A + T + Bt
                            idx2 = len(A) + len(T) + j
                            c['(x1b) 分母'] += 1
                            if orphan(S2, idx2): c['★ (x1b) ランダム A を付けても孤児'] += 1
                            else: c['⛔ (x1b) 親ができる'] += 1
    D = c['★ 分母: ブロック内で孤児な列']
    print('### 消費側 |R|=%d 行1<%d   Q 側の分母（5 本） %d   ブロック内の列 %d'
          % (L, R1, c['Q 側の分母（5 本）'], c['ブロック内の列']))
    print('    ★ 分母（ブロック内で孤児な列） %d (%.3f%% of 列)  [%.1fs]'
          % (D, 100*D/max(c['ブロック内の列'],1), time.time()-t0))
    print('    孤児の srow: ', dict(sorted((k[1], c[k]) for k in c
              if isinstance(k, tuple) and k[0] == '孤児の srow')))
    for k in ['★ (x1a) 塔を付けても孤児', '⛔ (x1a) 塔を付けると親ができる']:
        print(f'      {k:34s} {c[k]:9d} ({100*c[k]/max(D,1):8.4f}%)')
    print('    ★★ `j` で分ける（`j=0` は 1 列なので必ず孤児 ⟹ 分母を膨らませる）:')
    for jk in ('j=0', 'j>=1'):
        dd = c[(jk, '分母')]
        print('        %-6s 分母 %8d   ★ 孤児のまま %8d (%8.4f%%)   ⛔ 親ができる %8d (%8.4f%%)'
              % (jk, dd, c[(jk,'★ 孤児のまま')], 100*c[(jk,'★ 孤児のまま')]/max(dd,1),
                 c[(jk,'⛔ 親ができる')], 100*c[(jk,'⛔ 親ができる')]/max(dd,1)))
    b = c['(x1b) 分母']
    for k in ['★ (x1b) ランダム A を付けても孤児', '⛔ (x1b) 親ができる']:
        print(f'      {k:34s} {c[k]:9d} ({100*c[k]/max(b,1):8.4f}%)  ⚠ A ∈ W u は判定していない')
    print('    ⛔ 親のブロック（何個手前か。-1 = 同じブロック内）: ',
          dict(sorted((k[1], c[k]) for k in c
              if isinstance(k, tuple) and k[0] == '⛔ 親のブロック（手前へ何個）')))
    for x in ex:
        print(f'      ⛔ 反例 Q={x[0]} d={x[1]} e={x[2]} n={x[3]} 列 j={x[4]} srow={x[5]} '
              f'親={x[6]}（ブロック {x[7]}）')
        print(f'            合成列={x[8]}')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 511, 2)
    run(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3), 513, 3)
