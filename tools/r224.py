# -*- coding: utf-8 -*-
"""**課題 (z1) —— `OrphOK0`（`j = 0` 版）。**

## 的

「塔 `mTower Q d e (k+1)` の中で第 `(k+1)` ブロックの**根**が孤児」
⟹ 「`A ++ 塔 ++ 根 1 列`（＝ `A ++ mTower Q d e (k+2)` の該当位置）でも孤児」

⚠ 実装は「`T = mTower Q d e n`（`n = k+2`）の添字 `(k+1)*|Q|` が塔の中で孤児か」を前件にし、
`A ++ T` で同じ添字（`+|A|`）を見る。

## ⚠ (z1b) の主語の訂正（先に確かめた）

消費側の `Q = Lift1 ((0,v,z) :: R.dropLast) t` は **`entry Q 0 0 = 0`**（＝ `hbase`）。
⟹ **「`Q` の根より浅い列」は存在しない**（行 0 は自然数）。
⟹ (z1b) は「**ブロック根より浅い列**（行 0 < `entry Q 0 0 + d*k`）」で測る。
**⟹ (y1) の `A` にも「`Q` の根より浅い列」は入りようがなかった。** そこは報告する。

## `A` の 6 種

    (A0) 空 ／ (A1) 1 列ランダム ／ (A2) ★ 実例 `mTower ++ B.take p` ／ (A3) ランダム 3 列
    **(A4) ★★ 意図的に浅い 1 列 `(0, 0, 0)`**（行 0 が最小）
    **(A5) ★★ 意図的に浅い 3 列**（行 0 が 0..d*k-1 の範囲）

## ★ 予想（教訓 45）＋ 見積もり

> **⚠ (A4)(A5) は**ブロック根の行 0 より浅い**列なので `nextrel0` が発火しうる
>   ⟹ **破れる**と予想。見積もり **成立 40〜90%**。**
> **⚠ (A0)〜(A3) は (y1) と同じく 100% と予想。**
> **⚠ `e = 0` を必ず箱に入れる（team-lead の指定）。**
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


def orphan(S, j): return trio.parent(S, srow(S, j), j) is None


def run(L, R1, VS, ZS, TS, NS, ES, seed, tag):
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
                    d0 = dOf(M)
                    if not (d0 > 0 and hr0(Q) and Q[0][2] == 0): continue
                    LQ = len(Q)
                    for e in ES:            # ★ `e = 0` を必ず含む
                        ekey = 'e = 0' if e == 0 else 'e > 0'
                        for n in NS:
                            T = [tuple(x) for x in mTower(Q, d0, e, n)]
                            for k in range(1, n):
                                idx = k * LQ
                                if not orphan(T, idx): continue     # ★ 前件
                                c[(ekey, '★ 分母: 塔の中でブロック根が孤児')] += 1
                                deep = d0 * k          # ブロック根の行 0
                                n2 = rnd.choice(NS); p = rnd.randrange(LQ)
                                A2 = ([tuple(x) for x in mTower(Q, d0, e, n2)]
                                      + block(Q, d0, e, n2)[:p])
                                As = {
                                  '(A0) 空': [],
                                  '(A1) 1 列ランダム': [(rnd.randrange(6), rnd.randrange(6),
                                                    rnd.randrange(2))],
                                  '(A2) ★ 実例 塔++B.take p': A2,
                                  '(A3) ランダム 3 列': [(rnd.randrange(6), rnd.randrange(6),
                                                    rnd.randrange(2)) for _ in range(3)],
                                  '(A4) ★★ 浅い 1 列 (0,0,0)': [(0, 0, 0)],
                                  '(A5) ★★ 浅い 3 列': [(rnd.randrange(max(deep, 1)),
                                                     rnd.randrange(3), rnd.randrange(2))
                                                    for _ in range(3)],
                                }
                                for an, A in As.items():
                                    S = A + T
                                    c[(ekey, an, '分母')] += 1
                                    if orphan(S, len(A) + idx):
                                        c[(ekey, an, '★ 孤児のまま')] += 1
                                    else:
                                        c[(ekey, an, '⛔ 親ができる')] += 1
                                        par = trio.parent(S, srow(S, len(A) + idx),
                                                          len(A) + idx)
                                        w = ('A の中の第 %d 列' % par if par < len(A)
                                             else '塔の中')
                                        c[(ekey, an, '  ' + w)] += 1
                                        if len(ex) < 5:
                                            ex.append((an, ekey, Q, d0, e, n, k, A, par, w))
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    for ekey in ('e = 0', 'e > 0'):
        D = c[(ekey, '★ 分母: 塔の中でブロック根が孤児')]
        if not D: continue
        print(f'  {ekey}   ★ 分母（塔の中でブロック根が孤児）… {D}')
        for an in ['(A0) 空', '(A1) 1 列ランダム', '(A2) ★ 実例 塔++B.take p',
                   '(A3) ランダム 3 列', '(A4) ★★ 浅い 1 列 (0,0,0)', '(A5) ★★ 浅い 3 列']:
            dd = c[(ekey, an, '分母')]
            if not dd: continue
            print(f'      {an:28s} ★ 孤児のまま {c[(ekey,an,"★ 孤児のまま")]:8d} '
                  f'({100*c[(ekey,an,"★ 孤児のまま")]/dd:8.4f}%)   '
                  f'⛔ 親 {c[(ekey,an,"⛔ 親ができる")]:7d} '
                  f'({100*c[(ekey,an,"⛔ 親ができる")]/dd:8.4f}%)')
            for kk in sorted(x for x in c if len(x) == 3 and x[0] == ekey and x[1] == an
                             and x[2].startswith('  ')):
                print(f'          {kk[2].strip()}: {c[kk]}')
    for x in ex:
        print(f'      ⛔ 反例 {x[0]} / {x[1]} Q={x[2]} d={x[3]} e={x[4]} n={x[5]} k={x[6]} '
              f'A={x[7]} 親={x[8]}（{x[9]}）')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (2,3,4), (0,1,2), 611, '消費側 |R|=3 行1<3')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (2,3,4), (0,1,2), 613, '★ 消費側 |R|=4 行1<3')
