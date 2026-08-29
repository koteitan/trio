# -*- coding: utf-8 -*-
"""**課題 H64 (n1): `|R| = 1` の証明の骨は `|R| >= 2` のどこで折れるか。**

    `TowerExpBig`（`L105Cap.lean:2752`）
      ∀ v z m a R, argOK R → **2 <= |R|** → z <= 1 → 2v+z <= a →
        domT R m → **`R.dropLast ∈ Wstar`** →
        hasParent ((0,v,z) :: R) (srow R (|R|-1)) |R| →
        ∀ n >= 1, ((0,v,z) :: R)⟦n⟧ ∈ W a

`|R| = 1` の証明（`towerGraft2Single_holds`、仮定ゼロ・緑）の骨:

    `R.dropLast = []` ⟹ `graft R y` は行 0 をずらすだけ
    ⟹ **塔の全列の行 2 が根の `z` に等しい**
    ⟹ 末尾列は**必ず孤児**（行 2 が同じなら `nextrel2` の狭義増加が立たない）
    ⟹ `oper` は `Pred` ⟹ 根まで剥ける

`|R| >= 2` では `graft R y` の胴体に **`R.dropLast` が入る**ので、
その行 2 は `z` とは限らない ⟹ **行 2 の定数性が壊れる**はず。

**測るもの（(n1) 最優先）:**

    (n1a) `S⟦n⟧` の行 2 が定数（= `z`）である割合。`|R|` 別に
    (n1b) 定数性が壊れたとき、**末尾列は孤児のままか**
    (n1c) 孤児でなくなったとき `oper` は何になるか（`Pred` か、コピーか）

⚠ **`Trio.lean:98` の `oper` に合わせる**（`trio.expand` は長さ 1 で `[]` を返すので、
　長さ 1 は**恒等**に直して使う。R2 が踏んだ罠）。
⚠ 母集団は `TowerExpBig` の前提を満たすものだけ。**分母を必ず出す**（教訓 23）。
⚠ 教訓 21: 100% が出たら `|R|` を 1 段伸ばして壊す。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import fmt, entry, argOK, srow, has_parent, dom_m, levM
from collections import Counter


def oper(S, n):
    """`Trio.lean:98` の `oper`。**長さ 1 では恒等**（`trio.expand` は `[]` を返す）。"""
    if len(S) <= 1:
        return list(S)
    return trio.expand(list(S), n)


def main(lens=(2, 3), vmax=3, dmax=4, bmax=3, nmax=3, tag=''):
    cols = [(d, b, c) for d in range(1, dmax) for b in range(bmax)
            for c in range(2)]
    print('### 母集団%s（列 = 行0∈[1,%d]・行1<%d・行2<2、`|R|` = %s、`v < %d`）'
          % (tag, dmax - 1, bmax, list(lens), vmax))
    print()
    den = Counter()
    n1a = Counter()
    n1b = Counter()
    n1c = Counter()
    ex = []
    checked = 0
    for L in lens:
        for R in itertools.product(cols, repeat=L):
            R = list(R)
            m = dom_m(R)
            for v in range(vmax):
                for z in range(2):
                    checked += 1
                    # ---- `TowerExpBig` の前提（`R.dropLast ∈ Wstar` 以外の構文の分）
                    if m is None:                       # domT R m
                        den['`domT R m` を満たさない'] += 1
                        continue
                    S = [(0, v, z)] + R
                    if not has_parent(S, srow(R, len(R) - 1), len(R)):
                        den['根が復活させない（`hasParent` を満たさない）'] += 1
                        continue
                    den['**前提を満たした（分母）**'] += 1
                    for n in range(1, nmax + 1):
                        T = oper(S, n)
                        if not T:
                            n1a['`S⟦n⟧` が空'] += 1
                            continue
                        const2 = all(q[2] == z for q in T)
                        n1a['`|R|`=%d / 行 2 が定数（= z）: %s'
                            % (L, 'はい' if const2 else '**いいえ**')] += 1
                        j = len(T) - 1
                        orph = not has_parent(T, srow(T, j), j)
                        key = '定数' if const2 else '**非定数**'
                        n1b['`|R|`=%d / z=%d / %s ⟹ 末尾は孤児: %s'
                            % (L, z, key, 'はい' if orph else '**いいえ**')] += 1
                        if not orph:
                            n1c['`|R|`=%d / 孤児でない ⟹ `srow` = %d'
                                % (L, srow(T, j))] += 1
                            if len(ex) < 6:
                                ex.append((R, v, z, n, S, T))
    print('検査した `(R,v,z)`: **%d**' % checked)
    print()
    wref.tally(den, '前提の充足（教訓 23）')
    wref.tally(n1a, '(n1a) `S⟦n⟧` の行 2 は定数 `z` か')
    wref.tally(n1b, '(n1b) 定数性と「末尾が孤児か」')
    wref.tally(n1c, '(n1c) 孤児でないときの `srow`')
    for R, v, z, n, S, T in ex:
        print('    例: R=`%s` v=%d z=%d n=%d' % (fmt(R), v, z, n))
        print('        S   =`%s`' % fmt(S))
        print('        S⟦n⟧=`%s`' % fmt(T))
    print()


if __name__ == '__main__':
    print('## (n1) `|R| = 1` の骨（行 2 が定数 ⟹ 末尾は孤児 ⟹ `oper` は `Pred`）はどこで折れるか')
    print()
    main(lens=(1,), tag='（`|R|` = 1 —— 対照。ここでは骨が通るはず）')
    main(lens=(2,), tag='（`|R|` = 2）')
    main(lens=(3,), tag='（`|R|` = 3）')
    print('## ⚠ 教訓 21: `|R| = 4` で壊れないか')
    print()
    main(lens=(4,), vmax=2, dmax=3, bmax=2, tag='（`|R|` = 4、列の範囲は狭め）')
