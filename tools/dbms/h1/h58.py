# -*- coding: utf-8 -*-
"""**課題 H57-a: `WSnoc` と `WCat` に健全な反証器を当てる。**

この 2 本は**仮定が全部 `∈ W` の形**なので、`wref` の反証器で
**仮定も結論も同じ計器で測れる**（`TowerOK` のような `Wstar` の ∀ が無い）。

    `WCat`  (`Wtower2:1974`) `∀ u A B, A ∈ W u → B ∈ W u → A ++ B ∈ W u`
    `WSnoc` (`Wtower2:2049`) `∀ u C p, C ∈ W u → C ≠ [] →
                               hasParent (C++[p]) (srow (C++[p]) |C|) |C| → C++[p] ∈ W u`

`wcat_of_snoc`（`Wtower2`）で **`WSnoc → WCat`** なので、
**`WCat` に反例が出れば `WSnoc` も偽**（表から 2 本消える）。

## 近似の向き

仮定は `inW == True`（過大 ⟹ 仮定を認めやすい ⟹ 違反を見つけやすい）、
結論の違反は `inW == False`（**健全**）。⟹ **違反ゼロは強い結果。**

## 陰性対照（計器が違反を検出できることの確認）

    `WCat` から `B ∈ W u` を落とす  … 偽のはず ⟹ **違反が出なければ計器が死んでいる**
    `WSnoc` から `C ≠ []` を落とす  … 偽のはず ⟹ 同上
"""
import sys, itertools, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
import wref
from wref import Ref, fmt, srow, has_parent, levM
from collections import Counter

AMAX = 12
COLS = [(a, b, c) for a in range(4) for b in range(4) for c in range(2)]
SMALL = [(a, b, c) for a in range(3) for b in range(3) for c in range(2)]


def seqs(cols, lens):
    out = []
    for L in lens:
        for S in itertools.product(cols, repeat=L):
            out.append(list(S))
    return out


def run(ref, tag, lens, cols, extra=0, seed=20260830):
    rng = random.Random(seed)
    pool = seqs(cols, lens)
    if extra:
        pool += [[rng.choice(COLS) for _ in range(rng.randint(2, 6))]
                 for _ in range(extra)]
    print('### %s' % tag)
    print()
    print('母数の下ごしらえ: 候補列 **%d** 本' % len(pool))
    print()

    # ---- minstage を先に全部出す（`inW == True` が確定した段）
    ms = {}
    for S in pool:
        ms[tuple(map(tuple, S))] = ref.minstage(S, AMAX)
    dec = [S for S in pool if ms[tuple(map(tuple, S))] is not None]
    print('うち段が確定したもの: **%d**（未確定 %d は母集団から外す）'
          % (len(dec), len(pool) - len(dec)))
    print()

    # ================================================ WCat
    tot = Counter()
    ex = []
    ctl = Counter()
    for A in dec:
        mA = ms[tuple(map(tuple, A))]
        for B in dec:
            mB = ms[tuple(map(tuple, B))]
            u = max(mA, mB)
            if len(A) + len(B) > 8:
                continue
            r = ref.inW(A + B, u)
            k = '**違反**' if r is False else 'OK' if r is True else '未判定'
            tot[k] += 1
            if r is False and len(ex) < 6:
                ex.append((A, B, u))
            # 陰性対照: `B ∈ W u` を落とす（u = mA だけ）
            if mB > mA:
                r2 = ref.inW(A + B, mA)
                ctl['**違反**' if r2 is False
                    else 'OK' if r2 is True else '未判定'] += 1
    print('**`WCat`: `A ∈ W u → B ∈ W u → A ++ B ∈ W u`**')
    print()
    wref.tally(tot, '結果（u = max(minstage A, minstage B)）')
    for A, B, u in ex:
        print('    反例: A=`%s` B=`%s` u=%d' % (fmt(A), fmt(B), u))
    if ex:
        print()
    wref.tally(ctl, '陰性対照（`B ∈ W u` を落とした版。違反が出るべき）')

    # ================================================ WSnoc
    tot2 = Counter()
    ex2 = []
    ctl2 = Counter()
    rows = []
    for C in dec:
        if not C:
            continue
        mC = ms[tuple(map(tuple, C))]
        for p in cols:
            S = C + [p]
            j = len(C)
            if not has_parent(S, srow(S, j), j):
                tot2['（親なし: 仮定を満たさない）'] += 1
                continue
            for du in (0, 1, 2):
                u = mC + du
                r = ref.inW(S, u)
                k = '**違反**' if r is False else 'OK' if r is True else '未判定'
                tot2['u=minstage+%d / %s' % (du, k)] += 1
                if du == 0:
                    rows.append((k if k != '未判定' else '未判定', S))
                if r is False and len(ex2) < 6:
                    ex2.append((C, p, u))
    print('**`WSnoc`: 親がつく 1 列の追加は段を上げない**')
    print()
    wref.tally(tot2, '結果')
    for C, p, u in ex2:
        print('    反例: C=`%s` p=`(%d,%d,%d)` u=%d' % (fmt(C), p[0], p[1], p[2], u))
    if ex2:
        print()

    # 陰性対照: `C ≠ []` を落とす（C = [] なら `[] ∈ W u` は常に真）
    for p in cols:
        for u in range(0, 4):
            r = ref.inW([p], u)
            ctl2['**違反**' if r is False
                 else 'OK' if r is True else '未判定'] += 1
    wref.tally(ctl2, '陰性対照（`C ≠ []` を落とした版 = `[] ++ [p]`。違反が出るべき）')
    wref.degeneracy(rows)
    return tot, tot2


if __name__ == '__main__':
    ref = Ref(ns=(1, 2, 3), maxdepth=9, maxlen=34, maxnodes=60000)
    wref.print_controls(ref)
    print('## 母集団 1: 長さ 1..2、列 = 行0<3・行1<3・行2<2')
    print()
    run(ref, '短い母集団', (1, 2), SMALL)
    print()
    print('## 母集団 2: 長さ 1..3（長さで傾向が変わらないことを見る）')
    print()
    run(ref, '長い母集団', (1, 2, 3), SMALL)
