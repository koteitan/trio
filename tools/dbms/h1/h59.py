# -*- coding: utf-8 -*-
"""**課題 H57-b: `TowerOK` / `TowerOK1` / `TowerOK2` に健全な反証器を当てる。**

    def TowerOK : Prop :=
      ∀ (v z u0 a) (R), argOK R → R ≠ [] → z ≤ 1 → 2*v+z ≤ a →
        **Aop W u0 Wstar R** → (∃ m, domT R m) →
        hasParent ((0,v,z) :: R) (srow R (|R|-1)) |R| →
        ∀ n ≥ 1, ((0,v,z) :: R)⟦n⟧ ∈ W a

`TowerOK1` / `TowerOK2` はこれに `srow R (|R|-1) = 1` / `= 2` を足したもの。

## 仮定 `Aop W u0 Wstar R` の扱い（ここがこの測定の要）

`Wstar` は `∀ v z a` を走るので**厳密には決定できない**。そこで**過大**に取る:

    節 1  `|R| ≤ 1 ∧ lev R 0 = 0` … `∃m domT R m` と両立しない（lev ≥ 1 が要る）⟹ 起きない
    節 2  `∀ n ≥ 1, R⟦n⟧ ∈ Wstar`
          `domT R m` より **R の末尾は自分の行で孤児**なので `R⟦n⟧ = Pred R`。
          ⟹ `|R| ≥ 2` では **`R.dropLast ∈ Wstar`** ちょうど 1 本
          （`|R| = 1` では `oper` が恒等なので `R ∈ Wstar` 自身）
    節 3  `∃ m < u0, domT M m ∧ ∀ z' ∈ W m, based z' → graft R z' ∈ Wstar`
          `m` は `domT` から一意、`u0` は全称なので `u0 = m+1` と取れる。
          `∀ z'` は**有限 pool** で近似。

そして `X ∈ Wstar` は `∀ w ≤ VMAX, ∀ y ≤ 1, inW([(0,w,y)] ++ X, 2w+y) is True`
で近似する（`W` は段に単調なので `a = 2w+y` が拘束的な場合）。

**向き**: どの近似も「**仮定を認めやすく**する」側 ⟹ 母集団が広がる ⟹
**違反を見つけやすくなる**。だから「違反ゼロ」はこの向きで強い結果。
逆に違反が出たら、その 1 件について `Aop` を手で確かめ直す必要がある。

**結論の側は健全**: `inW(...) is False` は確定した非所属。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import (Ref, fmt, srow, has_parent, levM, dom_m, argOK, graft, based)
from collections import Counter

VMAX = 4          # `Wstar` の `∀ v` をここまで見る
NSC = (1, 2, 3)   # 結論の `∀ n ≥ 1` をここまで見る


def wstar(ref, X, vmax=VMAX):
    """`X ∈ Wstar` の近似。'yes'（vmax まで確定）/'no'（確定した破れ）/'?'。"""
    if not argOK(X):
        return 'yes'                    # `argOK X → ...` なので空虚に真
    out = 'yes'
    for w in range(vmax + 1):
        for y in range(2):
            r = ref.inW([(0, w, y)] + list(X), 2 * w + y)
            if r is False:
                return 'no'
            if r is None:
                out = '?'
    return out


def zpool(ref, m, maxlen=2):
    """`{z' | based z', z' ∈ W m}` の有限 pool（節 3 の `∀ z'` の近似）。"""
    cols = [(a, b, c) for a in range(3) for b in range(3) for c in range(2)]
    head = [(0, b, c) for b in range(3) for c in range(2)]
    out = [[]]
    for L in range(1, maxlen + 1):
        for h in head:
            for rest in itertools.product(cols, repeat=L - 1):
                z = [h] + list(rest)
                if ref.inW(z, m) is True:
                    out.append(z)
    return out


def aop_ok(ref, R, wcache, zp_cache, use_clause3=True):
    """`Aop W u0 Wstar R` の過大近似。('yes'/'no'/'?', どの節か) を返す。"""
    # ---- 節 2
    key = tuple(map(tuple, R[:-1] if len(R) >= 2 else R))
    if key not in wcache:
        wcache[key] = wstar(ref, list(key))
    c2 = wcache[key]
    if c2 == 'yes':
        return 'yes', '節2'
    # ---- 節 3
    if use_clause3:
        m = dom_m(R)
        if m is not None:
            if m not in zp_cache:
                zp_cache[m] = zpool(ref, m)
            bad = False
            unk = False
            for z in zp_cache[m]:
                r = wstar(ref, graft(R, z))
                if r == 'no':
                    bad = True
                    break
                if r == '?':
                    unk = True
            if not bad:
                return ('?' if unk else 'yes'), '節3'
    return ('?' if c2 == '?' else 'no'), '節2'


def main(lens=(1, 2, 3), cols=None, use_clause3=True, tag=''):
    ref = Ref(ns=(1, 2, 3), maxdepth=9, maxlen=34, maxnodes=60000)
    wref.print_controls(ref)
    if cols is None:
        cols = [(a, b, c) for a in range(1, 4) for b in range(3)
                for c in range(2)]

    # ---------------- 母数の見積り（走らせる前に数える）
    Rs = []
    for L in lens:
        for R in itertools.product(cols, repeat=L):
            R = list(R)
            if dom_m(R) is None:            # `∃ m, domT R m`
                continue
            Rs.append(R)
    print('## 母集団%s' % tag)
    print()
    print('列 = 行0∈[1,%d]・行1<%d・行2<2（`argOK` は構成から）、長さ %s'
          % (max(c[0] for c in cols), max(c[1] for c in cols) + 1, list(lens)))
    print()
    print('`∃ m, domT R m` を満たす `R`: **%d** 本' % len(Rs))
    print()

    wcache, zp_cache = {}, {}
    tot = Counter()
    bysrow = Counter()
    ex = []
    rows = []
    for R in Rs:
        s = srow(R, len(R) - 1)
        for v in range(3):
            for z in range(2):
                M = [(0, v, z)] + R
                if not has_parent(M, s, len(R)):
                    tot['根が復活させない（仮定を満たさない）'] += 1
                    continue
                st, cl = aop_ok(ref, R, wcache, zp_cache, use_clause3)
                if st == 'no':
                    tot['`Aop` が確定で破れる（仮定を満たさない）'] += 1
                    continue
                if st == '?':
                    tot['`Aop` が未判定（母集団から外す）'] += 1
                    continue
                for da in (0, 1):
                    a = 2 * v + z + da
                    verd = 'OK'
                    for n in NSC:
                        r = ref.inW(trio.expand(list(M), n), a)
                        if r is False:
                            verd = '**違反**'
                            break
                        if r is None:
                            verd = '未判定'
                    tot['a=2v+z+%d / %s' % (da, verd)] += 1
                    bysrow['srow=%d / %s' % (s, verd)] += 1
                    if da == 0:
                        rows.append((verd, M))
                    if verd == '**違反**' and len(ex) < 8:
                        ex.append((R, v, z, a, cl))
    print('**`TowerOK`（`Aop` は過大近似、結論の反証は健全）**')
    print()
    wref.tally(tot, '結果')
    wref.tally(bysrow, '`srow` 別（`srow=1` は `TowerOK1`、`srow=2` は `TowerOK2`）')
    for R, v, z, a, cl in ex:
        M = [(0, v, z)] + R
        print('    反例候補: R=`%s` v=%d z=%d a=%d（`Aop` は %s）'
              % (fmt(R), v, z, a, cl))
        print('              M=`%s`' % fmt(M))
    if ex:
        print()
    wref.degeneracy(rows)
    return tot


if __name__ == '__main__':
    main(lens=(1, 2, 3), tag='（短め）')
