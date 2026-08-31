# -*- coding: utf-8 -*-
"""**課題 (e3) —— `srow = 1` の段で `oper` が作る `V` の形。**

## 母集団（team-lead の指定）

消費側（`dOf`/`eOf`）から降りた段のうち、**足す列の `srow = 1`**（⟹ `d0 > 0`, `d1 = e' = 0`）。
箱は前回と同じ 3 つ。**規模は `r207.py` と同じ（最大 55 秒）ので走らせてよい。**

## ★ 予想（教訓 45）＋ 見積もり —— **(e3d) は 100% にならない**

> **⚠ §R176（`r189.py`）で「**非減少の段（`|V| >= |Q|`）の `srow` は 0 が 730、1 が 26,235**」
>   ＝ 非減少の 97.3% が `srow = 1`。⟹ `srow = 1` の段には `|V| = |Q|` が含まれる。**
> **⟹ **(e3d) `|V| < |Q|` は 100% にならない**。見積もり **85〜97%**。**
> **⚠ (e3a) `V` の行 1 が定数 … 見積もり 5〜30%。**
> **⚠ (e3c) `V` の行 2 が全部 0 … `srow = 1` は**足す列**の性質で、窓の中の列は無関係。
>   ⟹ 100% にならないと予想。見積もり 40〜80%。**
> **⚠ 反例（team-lead に有利な形）: (e3d) が 100%。そのとき `0 < e` が鎖から消える。**
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


def run(L, R1, VS, ZS, TS, NS, depth, beam, seed):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    rnd = random.Random(seed); c = Counter(); ex = []; t0 = time.time()
    vals = Counter()
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
                    front = [(tuple(Q), dOf(M), eOf(M))]
                    for dep in range(1, depth + 1):
                        nxt = set()
                        for (X, dd, ee) in front:
                            LX = len(X)
                            for n in NS:
                                for j in range(LX):
                                    T = [tuple(y) for y in mTower(list(X), dd, ee, n)]
                                    S = T + block(list(X), dd, ee, n)[:j + 1]
                                    last = len(S) - 1
                                    i1 = srow(S, last)
                                    r = step_det(list(X), dd, ee, n, j)
                                    if r is None or len(r[0]) < 2: continue
                                    V, d0, e0 = [tuple(y) for y in r[0]], r[1], r[2]
                                    nxt.add((tuple(V), d0, e0))
                                    c['全段'] += 1
                                    c[('srow', i1)] += 1
                                    if i1 != 1: continue
                                    c['★ srow = 1 の段'] += 1
                                    if d0 > 0: c['  d0 > 0'] += 1
                                    if e0 == 0: c['  e0 = 0'] += 1
                                    # (e3d)
                                    if len(V) < LX: c['★ (e3d) |V| < |Q|'] += 1
                                    elif len(V) == LX:
                                        c['⚠ (e3d) |V| = |Q|'] += 1
                                        if len(ex) < 3: ex.append((X, dd, ee, n, j, V))
                                    else: c['⚠⚠ (e3d) |V| > |Q|'] += 1
                                    # (e3a)(e3b)
                                    s1 = {p[1] for p in V}
                                    if len(s1) == 1: c['★ (e3a) V の行 1 が定数'] += 1
                                    vals[min(len(s1), 8)] += 1
                                    # (e3c)
                                    if all(p[2] == 0 for p in V): c['★ (e3c) V の行 2 が全部 0'] += 1
                        if not nxt: break
                        front = list(nxt)
                        if len(front) > beam:
                            rnd.shuffle(front); front = front[:beam]
    s1n = c['★ srow = 1 の段']
    print(f'### 消費側 |R|={L} 行1<{R1} 深さ<={depth}  全段 {c["全段"]}  '
          f'[{time.time()-t0:.1f}s]')
    print('    足す列の srow: ', dict(sorted((k[1], c[k]) for k in c if isinstance(k, tuple))))
    print(f'    ★ srow = 1 の段 … {s1n}')
    for k in ['  d0 > 0', '  e0 = 0', '★ (e3d) |V| < |Q|', '⚠ (e3d) |V| = |Q|',
              '⚠⚠ (e3d) |V| > |Q|', '★ (e3a) V の行 1 が定数', '★ (e3c) V の行 2 が全部 0']:
        print(f'      {k:30s} {c[k]:9d} ({100*c[k]/max(s1n,1):8.4f}%)')
    tv = sum(vals.values())
    print('      (e3b) `V` の行 1 の値の個数: ',
          {k: f'{100*v/max(tv,1):.1f}%' for k, v in sorted(vals.items())})
    for x in ex: print(f'      ⚠ |V|=|Q| の例 Q={x[0]} (d,e)=({x[1]},{x[2]}) n={x[3]} j={x[4]} V={x[5]}')
    print()


if __name__ == '__main__':
    run(2, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 2, 150, 411)
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 2, 100, 413)
    run(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3), 1, 60, 415)
