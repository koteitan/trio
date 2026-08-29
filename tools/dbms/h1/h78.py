# -*- coding: utf-8 -*-
"""**課題 H67 (b1)-(b4) ＝ H68 (m3): ブロッカーの割合 ＝ 残核の大きさ。**

⚠ **教訓 24（先に `grep`）を当てた:**

    `L105Cap.lean:2880` `TowerExpBigRow2` の**正確な前提**を読んだ
      （行 2 の条件は **`∃ p ∈ R.dropLast, p.2.2 ≠ z`**。`(0,v,z)::R` ではない）
    `Lcone.le1_zero_iff`（`Lcone.lean:36`、緑）… 根が狭義最浅なら
      **`le1 A 0 j ⟺ 行 0 祖先鎖の根以外の `y` が全部 `entry A 1 0 < entry A 1 y`**
      ⟹ **ブロッカー ＝ 行 1 が `v` 以下の非根の列**（`v = entry Q 1 0`）
    `L105Cap.lean:1671-1674` … `(Lift1 X d)⟦n⟧ = shTower Q d0 n` は既にある

## 測るもの

    (b1) `Q = (0,v,z) :: R.dropLast` にブロッカーがある割合  ← **残核の大きさそのもの**
    (b2) ある場合の本数（1 本が支配的か）
    (b3) `|R|` を伸ばすとどう動くか（教訓 21）
    (b4) ブロッカーが無いとき `Lift1 Q e` が本当に一様シフト `shiftr01 0 e Q` と一致するか

⚠ 母集団は `TowerExpBigRow2` の前提を**全部**（`R.dropLast ∈ Wstar` 以外の構文の分）。
⚠ 分母を必ず出す（教訓 23）。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import fmt, entry, srow, has_parent, dom_m, Lift1, shiftr01
from collections import Counter


def main(lens=(2, 3), vmax=3, dmax=4, bmax=4, tag=''):
    cols = [(d, b, c) for d in range(1, dmax) for b in range(bmax)
            for c in range(2)]
    print('### 母集団%s（列 = 行0∈[1,%d]・行1<%d・行2<2、`|R|` = %s、`v < %d`）'
          % (tag, dmax - 1, bmax, list(lens), vmax))
    print()
    den = Counter()
    b1 = Counter()
    b2 = Counter()
    b4 = Counter()
    ex = []
    checked = 0
    for L in lens:
        for R in itertools.product(cols, repeat=L):
            R = list(R)
            m = dom_m(R)
            for v in range(vmax):
                for z in range(2):
                    checked += 1
                    if m is None:
                        den['`domT R m` を満たさない'] += 1
                        continue
                    if srow(R, len(R) - 1) != 2:
                        den['`srow != 2`'] += 1
                        continue
                    S = [(0, v, z)] + R
                    if not has_parent(S, 2, len(R)):
                        den['根が復活させない'] += 1
                        continue
                    if not any(p[2] != z for p in R[:-1]):
                        den['`∃p ∈ R.dropLast, p.2.2 ≠ z` を満たさない'] += 1
                        continue
                    den['**前提を満たした（分母）**'] += 1
                    # ---- ブロッカー: `Q` の非根の列で 行 1 <= v
                    Q = [(0, v, z)] + R[:-1]
                    blk = [j for j in range(1, len(Q)) if Q[j][1] <= v]
                    b1['**ブロッカーが %s**'
                       % ('ある ⟹ **残核**' if blk else 'ない ⟹ 一様に潰れる')] += 1
                    if blk:
                        b2['本数 = %d' % len(blk)] += 1
                    else:
                        # ---- (b4) 一様シフトに潰れるか
                        e = entry(R, 1, len(R) - 1) - v
                        for ee in ([e] if e >= 1 else [1, 2]):
                            same = Lift1(Q, ee) == shiftr01(0, ee, Q)
                            b4['`Lift1 Q e` == `shiftr01 0 e Q`: %s'
                               % ('**はい**' if same else '**いいえ**')] += 1
                            if not same and len(ex) < 4:
                                ex.append((R, v, z, ee, Q))
    print('検査した `(R,v,z)`: **%d**' % checked)
    print()
    wref.tally(den, '前提の充足（教訓 23）')
    wref.tally(b1, '**(b1) ブロッカーの有無 ＝ 残核の大きさ**')
    wref.tally(b2, '(b2) ブロッカーの本数')
    wref.tally(b4, '(b4) ブロッカーが無いとき一様シフトに潰れるか')
    for R, v, z, ee, Q in ex:
        print('    潰れない例: R=`%s` v=%d z=%d e=%d Q=`%s`'
              % (fmt(R), v, z, ee, fmt(Q)))
    print()


if __name__ == '__main__':
    print('## H67 (b1)-(b4) ＝ H68 (m3): ブロッカーの割合')
    print()
    main(lens=(2,), tag='（`|R|` = 2）')
    main(lens=(3,), tag='（`|R|` = 3）')
    print('## ⚠ 教訓 21: `|R|` を伸ばして割合が動くか')
    print()
    main(lens=(4,), vmax=3, dmax=3, bmax=3, tag='（`|R|` = 4）')
    main(lens=(5,), vmax=2, dmax=3, bmax=3, tag='（`|R|` = 5）')
