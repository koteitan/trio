# -*- coding: utf-8 -*-
"""**課題 (z2) —— `hz0(V)` が破れる `V` のブロック根は行 2 の孤児か。**

## 見立て（team-lead）

`entry V 2 0 = 1` ⟹ 塔のブロック根の行 2 は全部 1（行 2 はリフトされない）
⟹ `srow(ブロック根) = 2` ⟹ `nextrel2` は `entry M 2 (親) < 1` を要求 ⟹ 親は行 2 = 0 の列
⟹ さらに `nextrel2` は `le1 M (親) (ブロック根)` も要求（`Trio.lean:63`）
⟹ **そこが通らなければ孤児 ⟹ 無料**

## ★ 予想（教訓 45）＋ 見積もり

> **⚠ §R196 で近い母集団（核の形）のブロック根 684,140 について「親なし 100%」を測っており、
>   その中の `srow = 2` は 11,040 件だった。⟹ 期待は高い。**
> **⚠ だが母集団が違う（あちらは `d1=0 ∧ d0>0 ∧ entry V 1 0 > 0`）。**
> **⚠ 見積もり **80〜100%**。100% とは決めつけない。**
> **⚠ 反例が出たら親の位置と行 2 の値を貼る。**

## 対照（★ 私が設計。「破れが出る形」で）

team-lead の案（`hz0` 成立の `V`）は `srow != 2` なので**空虚**になる。⟹ 別に作る:

    **対照 A**: 塔の中の **ブロック根でない**列で行 2 = 1 のものが行 2 の親を持つ割合
      ⟹ 0% でなければ、計器は「行 2 の親」を検出できている。
    **対照 B**: ランダムな列（塔でない）で行 2 = 1 の列が行 2 の親を持つ割合

## 分母（`Q` 側に課したもの）

**`TowerP''` の 5 本**を満たす消費側の `Q` から降りた窓 `V` で **`entry V 2 0 > 0`**。
その `V` について塔 `mTower V d0 e0 m` のブロック根 `k*|V|`（`k >= 1`）。
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
from r171 import step_det
from r201 import dOf, eOf
from r206 import hr0


def run(L, R1, VS, ZS, TS, NS, MS, tag):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    c = Counter(); ex = []; t0 = time.time(); bad = set()
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
                    if not (len(Q) >= 1 and d > 0 and e > 0 and hr0(Q) and Q[0][2] == 0):
                        continue
                    for n in NS:
                        for j in range(len(Q)):
                            r = step_det(Q, d, e, n, j)
                            if r is None or len(r[0]) < 2: continue
                            V, d0, e0 = [tuple(y) for y in r[0]], r[1], r[2]
                            if V[0][2] > 0:
                                bad.add((tuple(V), d0, e0))
    print(f'### {tag}   ★ 分母（`entry V 2 0 > 0` の `V`、重複除去）… {len(bad)}  '
          f'[集めるのに {time.time()-t0:.1f}s]')
    for (Vt, d0, e0) in bad:
        V = list(Vt); LV = len(V)
        c[('(z2c) (d0,e0)', (min(d0, 3), min(e0, 3)))] += 1
        for m in MS:
            T = [tuple(x) for x in mTower(V, d0, e0, m)]
            for k in range(1, m):
                idx = k * LV
                c['★ ブロック根'] += 1
                c[('ブロック根の srow', srow(T, idx))] += 1
                if srow(T, idx) != 2:
                    c['⚠ srow != 2（見立てと違う）'] += 1
                    continue
                c['分母: srow=2 のブロック根'] += 1
                par = trio.parent(T, 2, idx)
                if par is None:
                    c['★ (z2a) 行 2 の孤児（無料）'] += 1
                else:
                    c['⛔ (z2a) 行 2 の親がいる'] += 1
                    if len(ex) < 4: ex.append((V, d0, e0, m, k, idx, par, T[par]))
            # 対照 A: ブロック根でない、行 2 = 1 の列
            for idx in range(len(T)):
                if idx % LV == 0: continue
                if T[idx][2] == 0: continue
                if srow(T, idx) != 2: continue
                c['対照A の分母'] += 1
                if trio.parent(T, 2, idx) is not None: c['★ 対照A 行 2 の親がいる'] += 1
    # 対照 B: ランダム
    rnd = random.Random(701)
    for _ in range(200000):
        n2 = rnd.randrange(2, 8)
        S = [(rnd.randrange(9), rnd.randrange(9), rnd.randrange(2)) for _ in range(n2)]
        i = n2 - 1
        if S[i][2] == 0 or srow(S, i) != 2: continue
        c['対照B の分母'] += 1
        if trio.parent(S, 2, i) is not None: c['★ 対照B 行 2 の親がいる'] += 1
    D = c['分母: srow=2 のブロック根']
    print(f'    ★ ブロック根 {c["★ ブロック根"]}   ⚠ srow != 2 … {c["⚠ srow != 2（見立てと違う）"]}')
    print('    ブロック根の srow: ', dict(sorted((k[1], c[k]) for k in c
              if isinstance(k, tuple) and k[0] == 'ブロック根の srow')))
    print(f'    ★ 分母（srow=2 のブロック根）… {D}')
    for k in ['★ (z2a) 行 2 の孤児（無料）', '⛔ (z2a) 行 2 の親がいる']:
        print(f'      {k:30s} {c[k]:9d} ({100*c[k]/max(D,1):8.4f}%)')
    a, b = c['対照A の分母'], c['対照B の分母']
    print(f'    ★ 対照A（塔の中の非ブロック根、行2=1、srow=2）… 分母 {a}   '
          f'親がいる {c["★ 対照A 行 2 の親がいる"]} ({100*c["★ 対照A 行 2 の親がいる"]/max(a,1):7.3f}%) ← 鳴るべき')
    print(f'    ★ 対照B（ランダムな列）… 分母 {b}   '
          f'親がいる {c["★ 対照B 行 2 の親がいる"]} ({100*c["★ 対照B 行 2 の親がいる"]/max(b,1):7.3f}%) ← 鳴るべき')
    print('    (z2c) `(d0,e0)` の分布（3 は 3 以上）: ',
          dict(sorted((k[1], c[k]) for k in c if isinstance(k, tuple) and k[0] == '(z2c) (d0,e0)')))
    for x in ex:
        print(f'      ⛔ 反例 V={x[0]} (d0,e0)=({x[1]},{x[2]}) m={x[3]} k={x[4]} '
              f'ブロック根 idx={x[5]} 親={x[6]} 親の列={x[7]}')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), (2,3,4), '消費側 |R|=3 行1<3')
    run(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3), (2,3,4), '消費側 |R|=3 行1<5')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), (2,3,4), '★ 消費側 |R|=4 行1<3')
