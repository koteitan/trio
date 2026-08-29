# -*- coding: utf-8 -*-
"""**課題 H57-e: `CoreSingleton` を「増幅」して測る。**

## 1. まず訂正: **`CoreSingleton` と `CoreCap` は同値**

`lean/Lind.lean` は**両向き**を証明していて、`leanman check` は緑（exit 0）:

    `coreSingleton_of_cap  (h : CoreCap) : CoreSingleton`   `Lind.lean:181`
    `cap_of_coreSingleton  (h : CoreSingleton) : CoreCap`   `Lind.lean:195`

⟹ `CORES.md` が別々の極小元として並べている 2 本は**同じ命題**。
⟹ **H56 の 220 万件（`CoreCap`）は、そのまま `CoreSingleton` の測定である。**

## 2. 増幅: 単元だけでなく**任意の `based y`** で測れる

    `mem_GX_of_core (hs : CoreSingleton) {y} (hby : based y) : y ∈ GX`  `Lind.lean:135`（緑）

⟹ **`based y` の `GX` 義務が 1 本でも確定で破れれば `CoreSingleton` は偽**、
したがって `CoreCap` も偽。H56 は `y = [(0,b,c)]`（`i ≤ 1`）だけを見ていたので、
**網はここで一気に広がる**。

義務（`GX` の定義、`Gamma.lean:169` を展開）:

    `based y` → `argOK M` → `1 ≤ |M|` → `z ≤ 1` → `CtxOK M v z` →
    `i ≤ |y|` → `2(v+t)+z ≤ a` →
      **`Lift1 ((0,v,z) :: graft M (y.take i)) t ∈ W a`**

`CtxOK M v z`（`Gamma.lean:153`）:

    `∀ k < |M|, ∀ a t, 2(v+t)+z ≤ a → Lift1 ((0,v,z) :: M.take k) t ∈ W a`

`W` は段に単調なので `a = 2(v+t)+z` が拘束的。`t` は `0..TMAX` で見る。

**向き**: `CtxOK` は `inW == True`（過大 ⟹ 文脈を認めやすい ⟹ 違反を見つけやすい）、
結論の違反は `inW == False`（**健全**）。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import Ref, fmt, entry, argOK, graft, Lift1
from collections import Counter

TMAX = 2


def ctxOK(ref, M, v, z, tmax=TMAX):
    """`CtxOK M v z` の近似。'yes'（tmax まで確定）/'no'（確定した破れ）/'?'。"""
    out = 'yes'
    for k in range(len(M)):
        for t in range(tmax + 1):
            X = Lift1([(0, v, z)] + list(M[:k]), t)
            r = ref.inW(X, 2 * (v + t) + z)
            if r is False:
                return 'no'
            if r is None:
                out = '?'
    return out


def main(ylens=(1, 2, 3), mlens=(1, 2), tag=''):
    ref = Ref(ns=(1, 2, 3), maxdepth=9, maxlen=34, maxnodes=6000)
    wref.print_controls(ref)
    mcols = [(d, b, c) for d in range(1, 4) for b in range(3) for c in range(2)]
    ycols = [(d, b, c) for d in range(3) for b in range(3) for c in range(2)]
    Ms = []
    for L in mlens:
        for M in itertools.product(mcols, repeat=L):
            Ms.append(list(M))
    ys = []
    for L in ylens:
        for h in [(0, b, c) for b in range(3) for c in range(2)]:
            for rest in itertools.product(ycols, repeat=L - 1):
                ys.append([h] + list(rest))
    print('## 母集団%s' % tag)
    print()
    print('文脈 `M`（`argOK`、行0∈[1,3]・行1<3・行2<2、長さ %s）: **%d** 本'
          % (list(mlens), len(Ms)))
    print()
    print('データ `y`（`based`、長さ %s）: **%d** 本' % (list(ylens), len(ys)))
    print()
    ctxs = []
    st = Counter()
    for M in Ms:
        for v in range(3):
            for z in range(2):
                s = ctxOK(ref, M, v, z)
                st[s] += 1
                if s == 'yes':
                    ctxs.append((M, v, z))
    print('装備できた文脈 `(M,v,z)`: **%d** / %d（未判定 %d、確定で破れ %d）'
          % (len(ctxs), sum(st.values()), st['?'], st['no']))
    print()
    print('⟹ 事例の見積り: %d × %d × (i の数 ~%.1f) × %d 通りの t'
          % (len(ctxs), len(ys), sum(len(y) + 1 for y in ys) / len(ys), TMAX + 1))
    print()

    tot = Counter()
    byi = Counter()
    ex = []
    rows = []
    import random as _rnd, time as _t
    if len(ctxs) > 150:
        ctxs = _rnd.Random(7).sample(ctxs, 150)
        print('⟹ 文脈は無作為 **150** 本に絞る（全部だと %d 本で終わらない）'
              % st['yes'])
        print()
    t0 = _t.time()
    for ci, (M, v, z) in enumerate(ctxs):
        if ci % 25 == 0:
            sys.stderr.write('  ctx %d/%d  %.0fs\n' % (ci, len(ctxs), _t.time() - t0))
        for y in ys:
            for i in range(len(y) + 1):
                G = graft(M, y[:i])
                for t in range(TMAX + 1):
                    X = Lift1([(0, v, z)] + G, t)
                    a = 2 * (v + t) + z
                    if len(X) > 8:
                        tot['長すぎて外した'] += 1
                        continue
                    r = ref.inW(X, a)
                    k = ('**違反**' if r is False
                         else 'OK' if r is True else '未判定')
                    tot[k] += 1
                    byi['i=%d / %s' % (min(i, 3), k)] += 1
                    if t == 0:
                        rows.append((k, X))
                    if r is False and len(ex) < 8:
                        ex.append((M, v, z, y, i, t, a, X))
    print('**`CoreSingleton` の増幅版（`based y` すべての `GX` 義務）**')
    print()
    wref.tally(tot, '結果')
    wref.tally(byi, '`i`（`y.take i`）別 —— `i ≤ 1` が H56 の見ていた範囲')
    for M, v, z, y, i, t, a, X in ex:
        print('    **反例**: M=`%s` v=%d z=%d y=`%s` i=%d t=%d a=%d'
              % (fmt(M), v, z, fmt(y), i, t, a))
        print('              X=`%s`' % fmt(X))
    if ex:
        print()
    wref.degeneracy(rows)


if __name__ == '__main__':
    main(ylens=(1, 2), mlens=(1, 2), tag='（y 長さ 1..2）')
    print()
    main(ylens=(3,), mlens=(1,), tag='（y 長さ 3 だけ）')
