# -*- coding: utf-8 -*-
"""**課題 (y1) —— `OrphOK` の接頭辞つき版。**

## 的

    ブロック `B := Lift1 (shiftr01 (d*n) 0 Q) (e*n)` の中で列 `j` が孤児
    ⟹ **`A ++ mTower Q d e n ++ B.take (j+1)` の中でも孤児**

## ⚠ 分母（§R200 の教訓を適用）

**`j >= 1` だけ**。`j = 0` は `B.take 1` が 1 列なので「その中で孤児」が自明に真 ⟹ 空虚。
`Q` 側は **`TowerP''` の 5 本**（`0<|Q|` / `0<d` / `0<e` / `hr0` / `hz0`）。

## `A` の 4 種類

    (A0) 空
    (A1) 1 列（ランダム）
    **(A2) ★ 実例 `mTower Q d' e' n' ++ B'.take p`**（再帰で実際に現れる形）
    (A3) ランダム 3 列
⚠ **どれも `A ∈ W u` は判定していない**（規則）。**上位集合**である。

## ★ 予想（教訓 45）＋ 見積もり

> **⚠ §R200 でランダム `A` は数字を変えなかった（`j>=1` で 100%）。**
> **⚠ だが **実例の `A`（塔）は行 0 が小さい列を大量に持つ** ⟹ 親が生まれうる。**
> **⚠ 見積もり **60〜100%**。100% とは決めつけない（前回外した方向を根拠にしない）。**
> **⚠ (y1b) 陰性対照（孤児でない列は `A` つきでも親を持つか）… 100% を期待。**
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


def run(L, R1, VS, ZS, TS, NS, seed):
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
                    if not (len(Q) >= 1 and d > 0 and e > 0 and hr0(Q) and Q[0][2] == 0):
                        continue
                    for n in NS:
                        B = block(Q, d, e, n)
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        # `A` の 4 種
                        n2 = rnd.choice(NS); p = rnd.randrange(len(Q))
                        A2 = ([tuple(x) for x in mTower(Q, d, e, n2)]
                              + block(Q, d, e, n2)[:p])
                        As = {'(A0) 空': [],
                              '(A1) 1 列': [(rnd.randrange(6), rnd.randrange(6), rnd.randrange(2))],
                              '(A2) ★ 実例 塔++B.take p': A2,
                              '(A3) ランダム 3 列': [(rnd.randrange(6), rnd.randrange(6),
                                                 rnd.randrange(2)) for _ in range(3)]}
                        for j in range(1, len(Q)):     # ★ j >= 1 だけ
                            Bt = B[:j + 1]
                            isorph = orphan(Bt, j)
                            for an, A in As.items():
                                S = A + T + Bt
                                idx = len(A) + len(T) + j
                                if isorph:
                                    c[(an, '★ 分母: ブロック内で孤児 (j>=1)')] += 1
                                    if orphan(S, idx):
                                        c[(an, '★ (y1a) 孤児のまま')] += 1
                                    else:
                                        c[(an, '⛔ (y1a) 親ができる')] += 1
                                        par = trio.parent(S, srow(S, idx), idx)
                                        where = ('A の中' if par < len(A) else
                                                 ('塔の中（%d ブロック手前）'
                                                  % ((len(T)//len(Q)) - (par-len(A))//len(Q))
                                                  if par < len(A)+len(T) else 'ブロック内'))
                                        c[(an, '  親の位置: ' + where)] += 1
                                        if len(ex) < 4:
                                            ex.append((an, Q, d, e, n, j, par, where))
                                else:
                                    c[(an, '対照の分母: 孤児でない列')] += 1
                                    if not orphan(S, idx):
                                        c[(an, '★ (y1b) 親を持つまま')] += 1
                                    else:
                                        c[(an, '⚠ (y1b) 親を失う')] += 1
    print(f'### 消費側 |R|={L} 行1<{R1}   [{time.time()-t0:.1f}s]')
    for an in ['(A0) 空', '(A1) 1 列', '(A2) ★ 実例 塔++B.take p', '(A3) ランダム 3 列']:
        D = c[(an, '★ 分母: ブロック内で孤児 (j>=1)')]
        C = c[(an, '対照の分母: 孤児でない列')]
        print(f'  {an}   ★ 分母 {D}   対照の分母 {C}')
        print(f'      ★ (y1a) 孤児のまま   {c[(an,"★ (y1a) 孤児のまま")]:9d} '
              f'({100*c[(an,"★ (y1a) 孤児のまま")]/max(D,1):8.4f}%)   '
              f'⛔ 親ができる {c[(an,"⛔ (y1a) 親ができる")]:8d} '
              f'({100*c[(an,"⛔ (y1a) 親ができる")]/max(D,1):8.4f}%)')
        print(f'      ★ (y1b) 対照: 孤児でない列が親を持つまま {c[(an,"★ (y1b) 親を持つまま")]:9d} '
              f'({100*c[(an,"★ (y1b) 親を持つまま")]/max(C,1):8.4f}%)   '
              f'⚠ 親を失う {c[(an,"⚠ (y1b) 親を失う")]}')
        for k in sorted(x for x in c if x[0] == an and x[1].startswith('  親の位置')):
            print(f'        {k[1]}: {c[k]}')
    for x in ex:
        print(f'      ⛔ 反例 {x[0]} Q={x[1]} d={x[2]} e={x[3]} n={x[4]} j={x[5]} '
              f'親={x[6]}（{x[7]}）')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 521)
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 523)
    run(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3), 525)
