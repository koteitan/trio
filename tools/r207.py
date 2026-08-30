# -*- coding: utf-8 -*-
"""(b1) の切り直し —— H12 の `hd0e_of_hr0`（`hr0 ⟹ hd0e`、緑）を反映。

⟹ 測るのは L3 の言う **3 つ**（`hr0(V)` / `hz0(V)` / `hlp(V)`）＋
   `TowerP` に在って L3 の 3 つに入っていない **`0 < e`** / **`0 < d`** / **`hbase`**。

**⚠ `hlp` は単独では意味が無い**（`hd0e` で `c.0 = V[0].0 + d0` が決まり、
`hr0M` が `V[0].0 < c.0` すなわち `0 < d0` を要求する）。
⟹ **`0 < d0` を条件にした `hlp`** を測る。

## ★ 予想（教訓 45）
> **⚠ §R186 で (3)(4b) と (5) の数字が完全一致した ⟹ **`0 < d0` の下で `hlp` は 100%** と予想。**
> **⚠ `hr0(V)` 100%、`hz0(V)` 99.3〜99.6%、`0 < e0` が 18.8%（穴）。箱を広げて壊しにいく。**
"""
import sys, itertools, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1
from r169 import domT
from r171 import step_det
from r201 import dOf, eOf
from r206 import hr0, hbase, hz0


def hlp_ok(V, d0, bound=60):
    """`0 < d0` の下で `le1 (V ++ [c]) 0 |V|` を満たす `c` が在るか。`c.0 = V[0].0 + d0`。"""
    c0 = V[0][0] + d0
    hi = max(p[1] for p in V) + bound
    for c1 in range(hi + 1):
        for c2 in (0, 1):
            if trio.is_ancestor(list(V) + [(c0, c1, c2)], 1, 0, len(V)):
                return True
    return False


def run(L, R1, VS, ZS, TS, NS, depth, beam, seed):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    rnd = random.Random(seed); cc = {k: Counter() for k in range(0, depth + 1)}
    t0 = time.time()
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
                    front = [(tuple(Q), d, e)]
                    for dep in range(0, depth + 1):
                        if dep > 0:
                            nxt = set()
                            for (X, dd, ee) in front:
                                for n in NS:
                                    for j in range(len(X)):
                                        r = step_det(list(X), dd, ee, n, j)
                                        if r is None or len(r[0]) < 2: continue
                                        nxt.add((tuple(r[0]), r[1], r[2]))
                            if not nxt: break
                            front = list(nxt)
                            if len(front) > beam:
                                rnd.shuffle(front); front = front[:beam]
                        c = cc[dep]
                        for (X, dd, ee) in front:
                            X = list(X); c['単位'] += 1
                            if hr0(X): c['★ hr0(V)'] += 1
                            if hz0(X): c['★ hz0(V)'] += 1
                            if dd > 0:
                                c['0 < d'] += 1
                                if hlp_ok(X, dd): c['★ hlp（`0<d` の下で）'] += 1
                            if ee > 0: c['⚠ 0 < e'] += 1
                            if hbase(X): c['hbase'] += 1
                            N = [(p[0] - X[0][0], p[1], p[2]) for p in X]
                            if hbase(N): c['hbase（正規化後）'] += 1
    print(f'### 消費側 |R|={L} 行1<{R1} v∈{tuple(VS)} t∈{tuple(TS)} n∈{tuple(NS)}  '
          f'[{time.time()-t0:.1f}s]')
    for dep in range(0, depth + 1):
        c = cc[dep]; t = c['単位']
        if not t: continue
        nm = '消費側の Q' if dep == 0 else f'降りた V 深さ{dep}'
        print(f'  {nm}（単位 {t}）')
        for k in ['★ hr0(V)', '★ hz0(V)', '0 < d', '⚠ 0 < e', 'hbase', 'hbase（正規化後）']:
            print(f'      {k:22s} {c[k]:9d} ({100*c[k]/t:8.4f}%)')
        dn = c['0 < d']
        print(f'      {"★ hlp（0<d の下で）":22s} {c["★ hlp（`0<d` の下で）"]:9d} '
              f'/ {dn} ({100*c["★ hlp（`0<d` の下で）"]/max(dn,1):8.4f}%)')
    print()


if __name__ == '__main__':
    run(2, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 3, 200, 391)
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 3, 120, 393)
    print('#### 教訓 21: 箱を広げる')
    run(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3,4), 2, 60, 395)
