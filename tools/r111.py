# -*- coding: utf-8 -*-
"""**課題 R110 —— (α)(β)(γ)(δ) の 4 分割。(δ) が残核の最終的な大きさ。**

⚠ 教訓 25（**引く補題の前提と結論の段・向きを `file:line` から写す**）を実行した。
主語はブロック **`B = (0,v,z) :: R.dropLast`**（L3 の `block_mem_of_liftTieCore` の主語）:

    (α) `L53.liftStage_of_noTie`（`L53Subst:1665`、**緑・仮定ゼロ**）
        前提 `argOK R'` ∧ **`∀ p ∈ R', p.2.1 ≠ v`** ∧ `((0,v,z)::R') ∈ W m`
        結論 `Lift1 ((0,v,z)::R') d ∈ W (m + 2d)`     （`R'` は `B` の尾 ＝ `R.dropLast`）
    (β) `L53.liftTie_case_tieFree`（`:2615`、緑）
        前提 `X ∈ W m` ∧ **`1 <= entry X 1 0`（＝ `v>=1`）** ∧ **`TieFree X`**
        結論 `Lift1 X d ∈ W (m + 2d)`
    (γ) `L105.liftStage_of_zeroRow2`（`L105Cap:2036`、緑・仮定ゼロ）
        前提 **`∀ p ∈ X, p.2.2 = 0`** ∧ `X ∈ W m`
        結論 `Lift1 X d ∈ W (m + 2d)`
    (δ) それ以外 ＝ `L105.LiftTieCore`（`L105Cap:1815`）← **本当の残核**

    `TieFree X`（`Wtower2.lean:59`）= `∀ j, coneV X (entry X 1 0 - 1) j → le1 X 0 j`
    ⚠ 閾値は **`v - 1`**（`v` にすると空虚になる。H12 が §181 でその穴に落ちた）
    `coneV A vv j`（`Cgraft:301`）= `∀ y, y →*₀ j → vv < entry A 1 y`（`y=j` も `y=0` も含む）

母集団: `TowerExpBigRow2`（`L105Cap:2880`）の構文の前提を**全部** ＋ `srow = 2`。
⚠ `R.dropLast ∈ Wstar` は有限では判定できない（R94）ので落とした**上位集合**。

**箱を 2 つ回す**（H12 とのずれの切り分けを兼ねる）:
    R2   列 行0∈{1,2,3} × 行1∈{0,1,2,3} × 行2∈{0,1}（24 列）、`v∈{0..3}`、`z∈{0,1}`
    H12  列 行0∈{1,2}   × 行1∈{0,1,2}   × 行2∈{0,1}（12 列）、`v∈{0,1,2}`、`z∈{0,1}`
"""
import sys, itertools, random, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter


def lev(c):
    return 2 * c[1] + c[2]


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def anc0(S, j):
    out = [j]
    while True:
        p = trio.parent(S, 0, out[-1])
        if p is None:
            break
        out.append(p)
    return out


def coneV(X, vv, j):
    return all(vv < X[y][1] for y in anc0(X, j))


def tiefree(X):
    v0 = X[0][1]
    thr = v0 - 1 if v0 >= 1 else 0
    for j in range(len(X)):
        if coneV(X, thr, j) and not trio.is_ancestor(X, 1, 0, j):
            return False
    return True


def classify(B, v):
    """`B = (0,v,z) :: R.dropLast` を 4 分割（排他的、上から順に当てる）。"""
    tail = B[1:]
    blk = [p for p in tail if p[1] <= v]
    if not blk:
        return '0 ブロッカー無（一様シフト ⟹ W_shift で無料）'
    if all(p[1] != v for p in tail):
        return '(α) タイ無し（liftStage_of_noTie）'
    if v >= 1 and tiefree(B):
        return '(β) タイ ∧ TieFree（liftTie_case_tieFree）'
    if all(p[2] == 0 for p in B):
        return '(γ) 行 2 ≡ 0（liftStage_of_zeroRow2）'
    return '(δ) **LiftTieCore ← 本当の残核**'


def run(COL, VS, ZS, Ls, label, sample_from=5):
    rng = random.Random(20260830)
    print(f'### {label}')
    keys = ['0 ブロッカー無（一様シフト ⟹ W_shift で無料）',
            '(α) タイ無し（liftStage_of_noTie）',
            '(β) タイ ∧ TieFree（liftTie_case_tieFree）',
            '(γ) 行 2 ≡ 0（liftStage_of_zeroRow2）',
            '(δ) **LiftTieCore ← 本当の残核**']
    print(f'  {"|R|":>4s} {"分母":>9s} {"ブロッカー有":>10s} '
          f'{"(α)":>8s} {"(β)":>8s} {"(γ)":>7s} {"(δ)":>9s} {"(δ)率":>8s}')
    for L in Ls:
        smp = 300000 if L >= sample_from else None
        src = ([rng.choice(COL) for _ in range(L)] for _ in range(smp)) if smp \
            else (list(x) for x in itertools.product(COL, repeat=L))
        c = Counter(); n = 0; nblk = 0
        for R in src:
            if any(p[0] < 1 for p in R):
                continue
            j = len(R) - 1
            i1 = srow(R, j)
            if i1 != 2 or trio.parent(R, i1, j) is not None or lev(R[j]) - 1 < 0:
                continue
            for v in VS:
                for z in ZS:
                    if trio.parent([(0, v, z)] + R, i1, len(R)) is None:
                        continue
                    if not any(p[2] != z for p in R[:-1]):
                        continue                      # TowerExpBigRow2 の追加前提
                    n += 1
                    B = [(0, v, z)] + R[:-1]
                    k = classify(B, v)
                    c[k] += 1
                    if not k.startswith('0 '):
                        nblk += 1
        tag = '' if smp is None else '*'
        if n == 0:
            continue
        print(f'  {str(L)+tag:>4s} {n:9d} {nblk:10d} '
              f'{c[keys[1]]:8d} {c[keys[2]]:8d} {c[keys[3]]:7d} '
              f'{c[keys[4]]:9d} **{100*c[keys[4]]/n:6.2f}%**')
        print(f'       割合            {100*nblk/n:9.2f}% '
              f'{100*c[keys[1]]/n:7.2f}% {100*c[keys[2]]/n:7.2f}% '
              f'{100*c[keys[3]]/n:6.2f}%')
    print('  （* は 30 万文脈の標本。それ以外は全数）')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=5)
    a = ap.parse_args()
    Ls = tuple(range(2, a.L + 1))
    run([(d, b, c) for d in (1, 2) for b in (0, 1, 2) for c in (0, 1)],
        (0, 1, 2), (0, 1), Ls, '**H12 の箱**（12 列、v∈[0,2]）—— 直接比較用')
    run([(d, b, c) for d in (1, 2, 3) for b in (0, 1, 2, 3) for c in (0, 1)],
        (0, 1, 2, 3), (0, 1), Ls, '**R2 の箱**（24 列、v∈[0,3]）')
