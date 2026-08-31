# -*- coding: utf-8 -*-
"""**課題 (z4) —— `j >= 1` の段で、親が**ブロック根**になることはあるか。**

## 主語（`file:line` から）

塔 `mTower Q d e n` の第 `k` ブロックの根 ＝ 添字 `k*|Q|`（`k < n`）。
足す列 ＝ 添字 `n*|Q| + j`。親 `par < n*|Q| + j`。
**「親がブロック根」を 2 つに分ける:**

    **(a) `par = n*|Q|`** … いま足しているブロックの根（`§186` の `p = 0`）
    **(b) `par = k*|Q|`, `k < n`** … **塔の**前のブロックの根（`p_rel = 0`）

`L105Cap:13093` §186 は `hpj : p < j` なので、**`j >= 1` なら `p = 0` は許される**。

## ★ 予想（教訓 45）＋ 見積もり

> **⚠ L3 の予想は「無い」。私は **「ある」** と予想する。**
> **⚠ (a) は §186 が `p < j` を許すので `j >= 1` で普通に起きるはず。見積もり **10〜40%**。**
> **⚠ (b) は §R178 で「`hr0∧hz0` だと親がブロックの外が 9〜12%」と測っている。
>   そのうち `p_rel = 0` の分。見積もり **1〜5%**。**
> **⚠ 反例（L3 に有利な形）: 両方 0%。**

**箱**: (1) 一様 ＋ `hr0 ∧ hz0`、(2) **消費側**（`dOf`/`eOf` で `(d,e)` が決まる本番の形）。
**`W` 所属は判定しない。**
"""
import sys, random, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower, Lift1
from r141 import block
from r183 import hr0, hz0
from r169 import domT
from r201 import dOf, eOf


def probe(Q, d, e, n, j, c, tag):
    L = len(Q)
    T = [tuple(x) for x in mTower(Q, d, e, n)]
    S = T + block(Q, d, e, n)[:j + 1]
    last = len(S) - 1
    par = trio.parent(S, srow(S, last), last)
    if par is None: return
    c[(tag, 'j>=1 の段')] += 1
    if par == n * L:
        c[(tag, '⚠★ (a) 親 = いま足しているブロックの根')] += 1
    elif par < n * L and par % L == 0:
        c[(tag, '⚠★ (b) 親 = 塔の前のブロックの根')] += 1
    if par >= n * L: c[(tag, '   参考: 親は同じブロック')] += 1
    else:            c[(tag, '   参考: 親は塔の中')] += 1


def uniform(E, LS, NS, DE, nsamp, seed):
    rnd = random.Random(seed); c = Counter()
    for _ in range(nsamp):
        L = rnd.choice(LS)
        a = rnd.randrange(E - 1)
        Q = [(a, rnd.randrange(E), 0)] + \
            [(rnd.randrange(a + 1, E), rnd.randrange(E), rnd.randrange(2))
             for _ in range(L - 1)]
        assert hr0(Q) and hz0(Q)
        d, e = rnd.choice(DE), rnd.choice(DE)
        for n in NS:
            for j in range(1, L):
                probe(Q, d, e, n, j, c, f'一様+hr0∧hz0 値域<{E}')
    return c


def consumer(L, R1, VS, ZS, TS, NS):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    c = Counter()
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
                    for n in NS:
                        for j in range(1, len(Q)):
                            probe(Q, d, e, n, j, c, f'消費側 |R|={L} 行1<{R1}')
    return c


def show(c):
    tags = sorted({k[0] for k in c})
    for tag in tags:
        t = c[(tag, 'j>=1 の段')]
        print(f'### {tag}   `j >= 1` の段 {t}')
        for k in ['⚠★ (a) 親 = いま足しているブロックの根',
                  '⚠★ (b) 親 = 塔の前のブロックの根',
                  '   参考: 親は同じブロック', '   参考: 親は塔の中']:
            print(f'    {k:44s} {c[(tag,k)]:9d} ({100*c[(tag,k)]/max(t,1):7.4f}%)')
        print()


if __name__ == '__main__':
    t0 = time.time()
    for E in (6, 9, 12):
        show(uniform(E, (3,4,5,6,8), (1,2,3,4,5), range(E), 8000, 341))
    print('#### ★ 消費側（本番の形。`(d,e)` は `dOf`/`eOf`）')
    show(consumer(2, 3, (0,1,2), (0,1), (0,1,2), (1,2,3)))
    show(consumer(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3)))
    show(consumer(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3,4)))
    print(f'[{time.time()-t0:.1f}s]')
