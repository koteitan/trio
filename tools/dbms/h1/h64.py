# -*- coding: utf-8 -*-
"""**課題 H57-g: `WSnoc` / `WCat` を大きい母集団で測り直す（`h58` の続き）。**

`h58` の母集団 2（長さ 1..3）は `WCat` を全対で回すので `5830^2` になり終わらない。
ここでは

    `WCat` … `A` は全部、`B` は無作為標本（対の数を上限で切る）
    `WSnoc`… `C` は長さ 1..3 の全部、`p` は列の全部

にして、**長さごとに分けて**（教訓「短い母集団は核を小さく見せる」）測る。
陰性対照は `h63` の `WCat−1`（63270 違反）と、ここでの `C = []` 版。
"""
import sys, itertools, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import wref
from wref import Ref, fmt, srow, has_parent
from collections import Counter

AMAX = 12
CAP_PAIRS = 120000


def verd(r):
    return '**違反**' if r is False else 'OK' if r is True else '未判定'


def run(ref, lens, cols, seed=20260830):
    rng = random.Random(seed)
    pool = []
    for L in lens:
        for S in itertools.product(cols, repeat=L):
            pool.append(list(S))
    print('### 長さ %s（候補 %d 本）' % (list(lens), len(pool)))
    print()
    dec = [(S, ref.minstage(S, AMAX)) for S in pool]
    dec = [(S, u) for S, u in dec if u is not None]
    print('段が確定したもの: **%d**' % len(dec))
    print()

    # ---------------- WSnoc
    tot = Counter()
    ex = []
    rows = []
    for C, mC in dec:
        for p in cols:
            S = C + [p]
            j = len(C)
            if not has_parent(S, srow(S, j), j):
                tot['（親なし: 仮定を満たさない）'] += 1
                continue
            for du in (0, 1, 2):
                r = ref.inW(S, mC + du)
                tot['u=minstage+%d / %s' % (du, verd(r))] += 1
                if du == 0:
                    rows.append((verd(r), S))
                if r is False and len(ex) < 6:
                    ex.append((C, p, mC + du))
    wref.tally(tot, '`WSnoc`（親がつく 1 列の追加は段を上げない）')
    for C, p, u in ex:
        print('    **反例**: C=`%s` p=`(%d,%d,%d)` u=%d'
              % (fmt(C), p[0], p[1], p[2], u))
    if ex:
        print()

    # ---------------- WCat（対を上限で切る）
    tot2 = Counter()
    ex2 = []
    npair = 0
    for A, mA in dec:
        Bs = dec if len(dec) * len(dec) <= CAP_PAIRS else \
            [dec[rng.randrange(len(dec))] for _ in range(CAP_PAIRS // len(dec))]
        for B, mB in Bs:
            if len(A) + len(B) > 8:
                continue
            u = max(mA, mB)
            r = ref.inW(A + B, u)
            tot2[verd(r)] += 1
            npair += 1
            if r is False and len(ex2) < 6:
                ex2.append((A, B, u))
    wref.tally(tot2, '`WCat`（`u = max(minstage A, minstage B)`、対 %d 組）' % npair)
    for A, B, u in ex2:
        print('    **反例**: A=`%s` B=`%s` u=%d' % (fmt(A), fmt(B), u))
    if ex2:
        print()
    wref.degeneracy(rows)


if __name__ == '__main__':
    ref = Ref(ns=(1, 2, 3), maxdepth=9, maxlen=34, maxnodes=6000)
    wref.print_controls(ref)
    cols = [(a, b, c) for a in range(3) for b in range(3) for c in range(2)]
    print('## 長さごとに分けて測る（長さで傾向が変わらないことを見る）')
    print()
    for L in (1, 2, 3):
        run(ref, (L,), cols)
        print()
