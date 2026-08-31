# -*- coding: utf-8 -*-
"""**課題 H58: 残核 1 点に健全な反証器を集中させる。**

> **残核 = `z = 1` かつ `c = 1` かつ `srow = 2` かつ「親が根でない」**
> 主語 `S = Lift1 ((0,v,z) :: cap M b c) t`、結論 `S ∈ W a`（`2(v+t)+z <= a`）

`lean/L105Cap.lean` の読み:

    `tower2_stage_fits_of_lt`（`:1093`）… 段が収まる ⟺ **`z < c`**
    `tower2_root_z_lt`（`:1103`）      … 親が根なら `nextrel2` が `z < c` を自動で与える
    ⟹ **`z=1, c=1` のときだけ根が親の候補から外れ、`z < c` が使えない**

⚠ `L105Cap` §23（`tower2_not_z1_c1`）は「この点は**空虚**」と言うが、それは
**`TowerOK2` の設定（`domT R m` がある）**での話。`CoreCap` の snoc の残核では
`domT` が成り立たない（末尾に親がある）ので、**この点は生きている**（同 file §19.1）。
下の実測でも**空ではない**（`|M| = 2` で 1728 件、`|M| = 3` で 62208 件）。

**違反が 1 件でも出れば `CoreCap` は偽**、したがって `CoreSingleton` も偽
（`Lind.lean:181`/`:195` で同値）、`Final.lean:573` の停止性証明も無効になる。

## 健全性

    結論の `inW(...) is False` は **確定した非所属**（`Wchar.lean` の
      `mem_iff_oper_mem` :75 と `mem_iff_lev_le` :106。`NS ⊆ {n : n >= 1}`）
    仮定 `CtxOK` は `inW == True` で近似 ⟹ **過大に認める** ⟹ 母集団が広がる
      ⟹ 違反を見つけやすくなる ⟹ 「違反ゼロ」はこの向きで強い

## 対照

    陽性: `wref.CONTROLS`（`(0,2,0)(1,0,0)@0` ほか）が確定 非所属になること
    陰性: **同じ母集団・同じ予算**で段を 1 下げた版（`a - 1`）が鳴ること
    予算: 節点予算を 2 通り走らせて**違反の数が動かない**こと
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import Ref, fmt, srow, cap, Lift1, entry, argOK
from collections import Counter

TMAX = 2


def ctxOK(ref, M, v, z, tmax=TMAX):
    """`CtxOK M v z`（`Gamma.lean:153`）の近似。'yes'/'no'/'?'。"""
    out = 'yes'
    for k in range(len(M)):
        for t in range(tmax + 1):
            r = ref.inW(Lift1([(0, v, z)] + list(M[:k]), t), 2 * (v + t) + z)
            if r is False:
                return 'no'
            if r is None:
                out = '?'
    return out


def verd(r):
    return '**違反**' if r is False else 'OK' if r is True else '未判定'


def run(ref, lens, cols, vmax=4, bmax=4, tag='', limit=None):
    print('### %s（`maxnodes = %s`）' % (tag, ref.maxnodes))
    print()
    tot = Counter()
    ctl = Counter()
    shape = Counter()
    ex = []
    rows = []
    ctxcache = {}
    n_seen = 0
    t0 = time.time()
    for L in lens:
        for M in itertools.product(cols, repeat=L):
            M = list(M)
            for v in range(vmax):
                z = 1
                c = 1
                for b in range(bmax):
                    for t in range(TMAX + 1):
                        S = Lift1([(0, v, z)] + cap(M, b, c), t)
                        j = len(S) - 1
                        if srow(S, j) != 2:
                            shape['`srow != 2`'] += 1
                            continue
                        p = trio.parent(S, 2, j)
                        if p is None:
                            shape['親なし（孤児 ⟹ `oper` は `Pred`）'] += 1
                            continue
                        if p == 0:
                            shape['親が根（`z < c` が使える）'] += 1
                            continue
                        shape['**残核: 親が根でない**'] += 1
                        # ---- 仮定 `CtxOK M v z`
                        key = (tuple(map(tuple, M)), v, z)
                        if key not in ctxcache:
                            ctxcache[key] = ctxOK(ref, M, v, z)
                        cs = ctxcache[key]
                        if cs == 'no':
                            tot['`CtxOK` が確定で破れる（仮定を満たさない）'] += 1
                            continue
                        if cs == '?':
                            tot['`CtxOK` が未判定（それでも測る）'] += 1
                        n_seen += 1
                        if limit and n_seen > limit:
                            continue
                        for da in (0, 1):
                            a = 2 * (v + t) + z + da
                            r = ref.inW(S, a)
                            tot['a=2(v+t)+z+%d / %s' % (da, verd(r))] += 1
                            if da == 0:
                                rows.append((verd(r), S))
                            if r is False and len(ex) < 8:
                                ex.append((M, v, z, b, c, t, a, S, p))
                        # ---- 陰性対照: 段を 1 下げる
                        a0 = 2 * (v + t) + z
                        ctl[verd(ref.inW(S, a0 - 1))] += 1
        print('（`|M| = %d` まで %.0f 秒）' % (L, time.time() - t0))
    print()
    wref.tally(shape, '主語の形の内訳（`z = 1`, `c = 1` に固定して全数）')
    wref.tally(tot, '**残核の判定**')
    for M, v, z, b, c, t, a, S, p in ex:
        print('    ★★ **確定した反例**: M=`%s` v=%d z=%d b=%d c=%d t=%d a=%d 親=%d'
              % (fmt(M), v, z, b, c, t, a, p))
        print('        S=`%s`' % fmt(S))
    if ex:
        print()
        print('    ⟹ **`CoreCap` は偽。したがって `CoreSingleton` も偽**')
        print('       （`Lind.lean:181`/`:195` で同値）。')
        print()
    wref.tally(ctl, '陰性対照（**同じ主語・同じ予算**で段を 1 下げた版。違反が出るべき）')
    wref.degeneracy(rows)
    return tot


if __name__ == '__main__':
    cols = [(d, b, c) for d in range(1, 4) for b in range(4) for c in range(2)]
    print('## 計器と対照')
    print()
    ref = Ref(ns=(1, 2, 3), maxdepth=9, maxlen=34, maxnodes=6000)
    wref.print_controls(ref)
    print('## 母集団: `z = 1` かつ `c = 1`、列 = 行0∈[1,3]・行1<4・行2<2')
    print()
    print('`v < 4`, `b < 4`, `t <= 2` を全部。**残核は `|M| = 2` で 1728 件、'
          '`|M| = 3` で 62208 件**（数えてから走らせた）。')
    print()
    run(ref, (1, 2), cols, tag='`|M| <= 2`（全数）')
    print()
    run(ref, (3,), cols, tag='`|M| = 3`（全数）')
