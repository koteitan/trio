# -*- coding: utf-8 -*-
"""**課題 (p4) —— 平行移動は `le0` を保つか。**

## 的（team-lead の証明筋の ③）

    `a` がブロック `m` の位置 `x0` にあるとき、
    **`le0 T a ((k+1)|Q|)` ⟹ `le0 T (k|Q| + x0) ((k+1)|Q|)`**

`e = 0` なので `mTower Q d 0 n` のブロック `k` ＝ `shiftr01 (d*k) 0 Q`（行 0 だけ `+d*k`）。

## ★ 予想（教訓 45）＋ 見積もり —— **控えめに**

⚠ 直前に 2 連続で「あるはず」に賭けて外した（(p3a) 85〜100%→15〜24%、(p3b) 50〜90%→0%）。
⟹ **今回は機構を先に考える。**

    `nextrel0 M j0 j1` は `entry M 0 j0 < entry M 0 j1` **かつ**
    「間の列が全部 `entry M 0 j1` 以上」（`Trio.lean:42`、**間の列に依存**）。
    ⟹ 平行移動しても**間に挟まる列の集合が変わる**（ブロックをまたぐ本数が違う）。
    ⟹ **保たれる保証は無い。**

> **⚠ 見積もり (p4a) **60〜95%**。100% とは予想しない。**
> **⚠ (p4c)（同一ブロック内の平行移動）は**間の列も一様にずれる**ので **95〜100%** と予想。**
> **⚠ 反例が出たらそのまま貼る。**

## 規模（先に数える）

`|Q| <= 4`、`n <= 4` ⟹ 塔は最大 16 列。組 `(a, k)` は最大 `16 * 4 = 64` /（`Q`,`d`,`n`）。
母集団の `Q` は §R197 の核の窓（重複除去 12,007 / 60,337）＋ 一様な箱。
⟹ **数千万オーダーにはならない。走らせてよい。**
"""
import sys, itertools, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1, mTower
from r169 import domT
from r171 import step_det
from r201 import dOf, eOf
from r212 import conds, K8


def le0(T, a, b): return trio.is_ancestor(T, 0, a, b)


def probe(Q, d, NS, c, ex):
    L = len(Q)
    for n in NS:
        T = [tuple(x) for x in mTower(Q, d, 0, n)]
        for k in range(1, n):
            tgt = (k + 1) * L
            if tgt >= len(T): continue
            for a in range(k * L):
                if not le0(T, a, tgt): continue
                c['★ 分母A: le0 a (k+1)|Q| かつ a < k|Q|'] += 1
                m, x0 = divmod(a, L)
                if le0(T, k * L + x0, tgt):
                    c['★ (p4a) 平行移動先も le0'] += 1
                else:
                    c['⛔ (p4a) 平行移動先は le0 でない'] += 1
                    if len(ex) < 4: ex.append(('p4a', Q, d, n, m, x0, k, a))
        # (p4c) 同一ブロック内の平行移動
        for k in range(n):
            for m in range(n):
                if k == m: continue
                for x in range(L):
                    for y in range(x + 1, L):
                        p = le0(T, m * L + x, m * L + y)
                        q = le0(T, k * L + x, k * L + y)
                        c['分母C: 同一ブロック内の (x,y) 組'] += 1
                        if p == q: c['★ (p4c) 一致'] += 1
                        else:
                            c['⛔ (p4c) 不一致'] += 1
                            if len(ex) < 8: ex.append(('p4c', Q, d, n, m, x, y, k))


def run_core(L, R1, VS, ZS, TS, NS, MS, seed, cap):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    core = set(); t0 = time.time()
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
                    for n in NS:
                        for j in range(len(Q)):
                            r = step_det(Q, d, e, n, j)
                            if r is None or len(r[0]) < 2: continue
                            V2, d0, d1 = [tuple(y) for y in r[0]], r[1], r[2]
                            if d1 == 0 and d0 > 0 and V2[0][1] > 0:
                                core.add((tuple(V2), d0))
    core = list(core); random.Random(seed).shuffle(core)
    if len(core) > cap: core = core[:cap]
    c = Counter(); ex = []
    for (Vt, d0) in core:
        probe(list(Vt), d0, MS, c, ex)
    print(f'### 核の窓 |R|={L} 行1<{R1}   `Q` として使った窓 {len(core)}  [{time.time()-t0:.1f}s]')
    show(c, ex)


def run_uniform(E, LS, DS, MS, nsamp, seed):
    rnd = random.Random(seed); c = Counter(); ex = []; t0 = time.time()
    for _ in range(nsamp):
        L = rnd.choice(LS)
        a = rnd.randrange(E - 1)
        Q = [(a, rnd.randrange(E), 0)] + \
            [(rnd.randrange(a + 1, E), rnd.randrange(E), rnd.randrange(2))
             for _ in range(L - 1)]
        probe(Q, rnd.choice(DS), MS, c, ex)
    print(f'### 一様（`hr0`＋`hz0`）値域<{E} |Q|∈{LS} d∈{tuple(DS)}   `Q` {nsamp}  '
          f'[{time.time()-t0:.1f}s]')
    show(c, ex)


def show(c, ex):
    A, C = c['★ 分母A: le0 a (k+1)|Q| かつ a < k|Q|'], c['分母C: 同一ブロック内の (x,y) 組']
    print(f'    ★ 分母A（`le0 a ((k+1)|Q|)` かつ `a < k|Q|`）… {A}')
    for k in ['★ (p4a) 平行移動先も le0', '⛔ (p4a) 平行移動先は le0 でない']:
        print(f'      {k:34s} {c[k]:9d} ({100*c[k]/max(A,1):8.4f}%)')
    print(f'    分母C（同一ブロック内の `(x,y)` 組）… {C}')
    for k in ['★ (p4c) 一致', '⛔ (p4c) 不一致']:
        print(f'      {k:34s} {c[k]:9d} ({100*c[k]/max(C,1):8.4f}%)')
    for x in ex[:5]:
        print(f'      ⛔ 反例 {x[0]}: Q={x[1]} d={x[2]} n={x[3]} 他={x[4:]}')
    print()


if __name__ == '__main__':
    run_uniform(6, (2,3,4), (1,2,3), (2,3,4), 4000, 481)
    run_uniform(9, (2,3,4,5), (1,2,3,4), (2,3,4), 3000, 483)
    run_core(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), (2,3,4), 485, 3000)
