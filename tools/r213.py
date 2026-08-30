# -*- coding: utf-8 -*-
"""**課題 (p2) —— `d1 = 0` の窓で `entry V 1 0 = 0` か。**

## 分母（`Q` 側に課したものを明記。教訓）

**`Q` 側 = `TowerP''(Q)` の 8 本すべてを満たす消費側の `Q`**（`h1out` は**訂正後**の形）。
そこから `oper` で降りた窓 `V`。さらに各測定ごとに分母を絞る（下に件数を出す）。

## ★ 予想（教訓 45）＋ 見積もり

> **⚠ (p2a) **100% にならない**と予想。§R193 の反例 `V = [(1,1,0), (2,0,0), (3,1,0)]` は
>   `entry V 1 0 = 1 > 0`（そして `d1 = 0`）。⟹ 見積もり **20〜60%**。**
> **⚠ (p2b) `srow(ブロック根) = 0` が (p2a) と同率、1 が残り、2 は ~0（`hz0(V)` が 99%）。**
> **⚠ (p2c) **100%** と予想（§R186 で `d0 = 0` は `srow = 0` と件数が完全一致していた）。**
> **⚠ (p2d) 反例はすぐ出るはず。貼る。**
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
from r171 import step_det
from r201 import dOf, eOf
from r212 import conds, K8, K7


def blockroot_srow(V, d0, d1):
    """次の塔 `mTower V d0 d1 m` のブロック根 `(V[0].0+d0*k, V[0].1+d1*k, V[0].2)` の `srow`。
    `k` に依らない（行 2 は不変、行 1 は `d1=0` なら不変）ので `k=0` で見る。"""
    return 2 if V[0][2] > 0 else (1 if V[0][1] > 0 else 0)


def run(L, R1, VS, ZS, TS, NS, depth, beam, seed):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    rnd = random.Random(seed); c = Counter(); ex = []; exc = []; t0 = time.time()
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
                    if not all(conds(Q, d, e)[k] for k in K8): continue
                    c['Q 側の分母: TowerP2(Q)'] += 1
                    front = [(tuple(Q), d, e)]
                    for dep in range(1, depth + 1):
                        nxt = set()
                        for (X, dd, ee) in front:
                            LX = len(X)
                            for n in NS:
                                for j in range(LX):
                                    # 足す列の srow（(p2c) の確認用）
                                    S = ([tuple(y) for y in mTower(list(X), dd, ee, n)]
                                         + block(list(X), dd, ee, n)[:j + 1])
                                    i1 = srow(S, len(S) - 1)
                                    r = step_det(list(X), dd, ee, n, j)
                                    if r is None or len(r[0]) < 2: continue
                                    V, d0, d1 = [tuple(y) for y in r[0]], r[1], r[2]
                                    c['窓 V（全体）'] += 1
                                    # ---- (p2a)(p2b) 分母 = d1 = 0 の窓 ----
                                    if d1 == 0:
                                        c['★ 分母A: d1 = 0 の窓'] += 1
                                        if V[0][1] == 0: c['★ (p2a) entry V 1 0 = 0'] += 1
                                        else:
                                            c['⛔ (p2a) entry V 1 0 > 0'] += 1
                                            if len(ex) < 4: ex.append((V, d0, d1, i1))
                                        c[('(p2b) ブロック根の srow', blockroot_srow(V, d0, d1))] += 1
                                    # ---- (p2c) 分母 = d0 = 0 の窓 ----
                                    if d0 == 0:
                                        c['★ 分母B: d0 = 0 の窓'] += 1
                                        if i1 == 0: c['★ (p2c) 足す列の srow = 0'] += 1
                                        else:
                                            c['⛔ (p2c) srow ≠ 0'] += 1
                                            if len(exc) < 3: exc.append((X, dd, ee, n, j, i1, V))
                                        if d1 == 0: c['   (p2c) d1 も 0'] += 1
                                    if all(conds(V, d0, d1)[k] for k in K7):
                                        nxt.add((tuple(V), d0, d1))
                        if not nxt: break
                        front = list(nxt)
                        if len(front) > beam:
                            rnd.shuffle(front); front = front[:beam]
    A, B = c['★ 分母A: d1 = 0 の窓'], c['★ 分母B: d0 = 0 の窓']
    print('### 消費側 |R|=%d 行1<%d 深さ<=%d   Q 側の分母 TowerP2(Q) … %d   窓 V（全体） %d  [%.1fs]'
          % (L, R1, depth, c['Q 側の分母: TowerP2(Q)'], c['窓 V（全体）'], time.time() - t0))
    print(f'  ★ 分母A（`d1 = 0` の窓）… {A}')
    print(f'      ★ (p2a) entry V 1 0 = 0   {c["★ (p2a) entry V 1 0 = 0"]:9d} '
          f'({100*c["★ (p2a) entry V 1 0 = 0"]/max(A,1):8.4f}%)')
    print(f'      ⛔ (p2a) entry V 1 0 > 0   {c["⛔ (p2a) entry V 1 0 > 0"]:9d} '
          f'({100*c["⛔ (p2a) entry V 1 0 > 0"]/max(A,1):8.4f}%)')
    print('      (p2b) ブロック根の srow: ',
          {k[1]: f'{c[k]} ({100*c[k]/max(A,1):.4f}%)' for k in sorted(
              x for x in c if isinstance(x, tuple))})
    print(f'  ★ 分母B（`d0 = 0` の窓）… {B}')
    for k in ['★ (p2c) 足す列の srow = 0', '⛔ (p2c) srow ≠ 0', '   (p2c) d1 も 0']:
        print(f'      {k:28s} {c[k]:9d} ({100*c[k]/max(B,1):8.4f}%)')
    for x in ex: print(f'      ⛔ (p2d) 反例 V={x[0]} (d0,d1)=({x[1]},{x[2]}) 足す列の srow={x[3]}'
                       f'  ⟹ entry V 1 0 = {x[0][0][1]}')
    for x in exc: print(f'      ⛔ (p2c) 反例 Q={x[0]} (d,e)=({x[1]},{x[2]}) n={x[3]} j={x[4]} srow={x[5]}')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 2, 100, 451)
    run(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3), 2, 60, 453)
