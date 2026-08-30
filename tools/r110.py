# -*- coding: utf-8 -*-
"""**課題 R109（team-lead 番号。私の §R109 と衝突するので §R110）—— `zle1` 後の残核。**

⚠ 教訓 24（先に `grep`）＋ 教訓 25（**引く補題の結論の段と向きを書き下す**）を実行した:

    `L105.tower_of_row2const`（`L105Cap.lean`、**緑・仮定ゼロ**）
      前提: `argOK R` ∧ `R≠[]` ∧ `2v+z <= a` ∧ `domT R m` ∧
            **`∀ p ∈ R.dropLast, p.2.2 = z`** ∧ `hasParent ((0,v,z)::R) (srow …) |R|`
      結論: **`∀ n>=1, ((0,v,z)::R)⟦n⟧ ∈ W a`** —— **塔そのもの。段は与えられた `a` のまま
            （上げない）。`srow = 1` でも `2` でも効く。**

    `L105.liftStage_of_zeroRow2`（`L105Cap:2036`、緑・仮定ゼロ）
      前提: `∀ p ∈ X, p.2.2 = 0` ∧ `X ∈ W m`
      結論: **`Lift1 X d ∈ W (m + 2*d)`** —— **主語は `Lift1 X d`（塔ではない）。段は `+2d`。**

⟹ **塔の枝を閉じるのは `tower_of_row2const` のほう**（`= z` で効き、`z` が 1 でもよく、段を上げない）。
   team-lead は (z2) で `liftStage_of_zeroRow2` を挙げたが、**それは別の補題**（`=0` 限定・段が動く）。

⟹ `TowerExpBig` の母集団は 2 つに割れる:

    `∀ p ∈ R.dropLast, p.2.2 = z`   … **`tower_of_row2const` で無料**
    `∃ p ∈ R.dropLast, p.2.2 ≠ z`   … **`TowerExpBigRow2` ＝ 残核**

  (z2) ★ 前者の割合はいくらか（＝ `zle1` 後に無料で片づく範囲）
  (z1)   残核の中でブロッカーありの割合（`|R|` 別）
  (z3)   ブロッカーの行 1 は `v` ちょうどか `v` 未満か（`liftStage_of_noTie` が効くのは `v` 未満だけ）

⚠ 教訓 21 の正しい適用: **箱（列アルファベット）を固定して `|R|` だけ動かす**。
   列 行0∈{1,2,3} × 行1∈{0,1,2,3} × 行2∈{0,1}（`zle1`）、`v∈{0,1,2,3}`、`z∈{0,1}`。
"""
import sys, itertools, random, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter


def lev(c):
    return 2 * c[1] + c[2]


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


COL = [(d, b, c) for d in (1, 2, 3) for b in (0, 1, 2, 3) for c in (0, 1)]
VS, ZS = (0, 1, 2, 3), (0, 1)


def sweep(L, sample, rng):
    """`TowerExpBig` の前提 ＋ `zle1` ＋ `srow=2` を満たすものを列挙。"""
    src = ([rng.choice(COL) for _ in range(L)] for _ in range(sample)) if sample \
        else (list(x) for x in itertools.product(COL, repeat=L))
    for R in src:
        if any(p[0] < 1 for p in R):
            continue
        j = len(R) - 1
        i1 = srow(R, j)
        if i1 != 2:
            continue
        if trio.parent(R, i1, j) is not None or lev(R[j]) - 1 < 0:
            continue
        for v in VS:
            for z in ZS:
                if trio.parent([(0, v, z)] + R, i1, len(R)) is None:
                    continue
                yield R, v, z


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=6)
    a = ap.parse_args()
    rng = random.Random(20260830)
    print('### R110 `zle1` 後の残核（箱を固定して `|R|` だけ動かす）')
    print('  列 行0∈{1,2,3}×行1∈{0..3}×行2∈{0,1}、v∈{0..3}、z∈{0,1}、`srow=2`')
    print('  ⚠ `R.dropLast ∈ Wstar` は有限では判定できない（R94）ので落とした**上位集合**')
    print()
    hdr = (f'  {"|R|":>4s} {"母数":>10s} {"z=1":>7s} '
           f'{"行2≡z(無料)":>12s} {"残核":>10s} {"残核率":>8s} '
           f'{"ブロッカーあり":>12s} {"率":>7s}')
    print(hdr)
    z3 = Counter()
    for L in range(2, a.L + 1):
        smp = 400000 if L >= 5 else None
        tot = free = core = blk = z1cnt = 0
        for R, v, z in sweep(L, smp, rng):
            tot += 1
            if z == 1:
                z1cnt += 1
            if all(p[2] == z for p in R[:-1]):
                free += 1
                continue
            core += 1
            bl = [p for p in R[:-1] if p[1] <= v]
            if bl:
                blk += 1
                for p in bl:
                    z3[('= v' if p[1] == v else '< v')] += 1
        tag = '' if smp is None else '*'
        print(f'  {str(L)+tag:>4s} {tot:10d} {z1cnt:7d} '
              f'{free:12d} {core:10d} {100*core/max(tot,1):7.2f}% '
              f'{blk:12d} {100*blk/max(core,1):6.2f}%')
    print('  （* は 40 万文脈の標本。それ以外は全数）')
    print()
    print('  -- (z3) ブロッカーの行 1（残核の中、全 `|R|` 合計） --')
    s = sum(z3.values())
    for k in sorted(z3):
        print(f'     行 1 {k:5s} : {z3[k]:10d}  ({100*z3[k]/max(s,1):5.2f}%)')
