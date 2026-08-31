# -*- coding: utf-8 -*-
"""**課題 H71: 残核を (α)(β)(γ)(δ) に 4 分割する。(δ) が本当の残核の大きさ。**

⚠ **前提は全部 `file:line` から写した**（教訓 25 の拡張。緑の補題を実測で検証するときは
　前提を写してから測る。R2 が false alarm を出した穴）:

    (0) ブロッカー無し … `Lcone.le1_zero_iff`（`Lcone.lean:36`）
        ⟹ ブロッカー ＝ **行 1 が `v` 以下の非根の列**。無ければ `Lift1` は一様シフト（§210）
    (γ) **`∀ p ∈ Q, p.2.2 = 0`** … `L105.liftStage_of_zeroRow2`（`L105Cap.lean:2036`、仮定ゼロ）
    (α) **`∀ p ∈ R.dropLast, p.2.1 ≠ v`** … `L53.liftStage_of_noTie_zero/_pos`
        （`L53Subst.lean:1618` / `:1654`、仮定ゼロ）⚠ 条件は **`R`（ここでは `R.dropLast`）の上**
    (β) **`1 <= v` ∧ `TieFree Q`** … `L53.liftTie_case_tieFree`（`L53Subst.lean:2615`）
        ⚠ **`1 <= entry X 1 0`（＝ `v >= 1`）が要る。`v = 0` では使えない**
    (δ) 残り ＝ **`LiftTieCore` そのもの ← 本当の残核**

主語のブロックは **`Q = (0,v,z) :: R.dropLast`**（L3 の `B`）。
⚠ **`TieFree` の閾値は `v-1`**（`Wtower2.lean:33` から写した。`v` にすると空虚。§181 の穴）。
⚠ 分母を必ず（教訓 23）。⚠ 箱を固定して `|R|` だけ動かす（教訓 21）。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import fmt, entry, srow, has_parent, dom_m
from h70 import tieFree
from collections import Counter


def classify(R, v, z):
    """`(0,v,z) :: R.dropLast` を (0)(γ)(α)(β)(δ) に分ける。"""
    Q = [(0, v, z)] + list(R[:-1])
    D = list(R[:-1])
    blk = [j for j in range(1, len(Q)) if Q[j][1] <= v]
    if not blk:
        return '(0) ブロッカー無し ⟹ 一様に潰れる（§210）'
    if all(p[2] == 0 for p in Q):
        return '(γ) 行 2 ≡ 0 ⟹ `liftStage_of_zeroRow2`（仮定ゼロ）'
    if all(p[1] != v for p in D):
        return '(α) タイ無し ⟹ `liftStage_of_noTie`（仮定ゼロ）'
    if v >= 1 and tieFree(Q):
        return '(β) タイあり ∧ `TieFree` ⟹ `liftTie_case_tieFree`'
    return '**(δ) タイ ∧ ¬`TieFree` ∧ 行 2 に非零 ＝ 本当の残核**'


def raw(R, v, z):
    """排他化しない生の該当（重複を見るため）。"""
    Q = [(0, v, z)] + list(R[:-1])
    D = list(R[:-1])
    return {
        'ブロッカー無し': not [j for j in range(1, len(Q)) if Q[j][1] <= v],
        '行 2 ≡ 0': all(p[2] == 0 for p in Q),
        'タイ無し': all(p[1] != v for p in D),
        '`1<=v` ∧ `TieFree`': v >= 1 and tieFree(Q),
    }


def main():
    cols = [(d, b, c) for d in range(1, 3) for b in range(3) for c in range(2)]
    print('## H71: 残核の 4 分割（箱を固定して `|R|` だけ動かす）')
    print()
    print('列 = 行0∈[1,2]・行1<3・行2<2（12 列）、`v<3`、`z<=1`。'
          'ブロック `Q = (0,v,z) :: R.dropLast`')
    print()
    rows = {}
    rawagg = {}
    for L in (2, 3, 4, 5):
        c = Counter()
        rr = Counter()
        for R in itertools.product(cols, repeat=L):
            R = list(R)
            if dom_m(R) is None:
                continue
            if srow(R, len(R) - 1) != 2:
                continue
            for v in range(3):
                for z in range(2):
                    S = [(0, v, z)] + R
                    if not has_parent(S, 2, len(R)):
                        continue
                    if not any(p[2] != z for p in R[:-1]):
                        continue
                    c[classify(R, v, z)] += 1
                    for k, ok in raw(R, v, z).items():
                        if ok:
                            rr[k] += 1
                    rr['**合計**'] += 1
        rows[L] = c
        rawagg[L] = rr
    keys = ['(0) ブロッカー無し ⟹ 一様に潰れる（§210）',
            '(γ) 行 2 ≡ 0 ⟹ `liftStage_of_zeroRow2`（仮定ゼロ）',
            '(α) タイ無し ⟹ `liftStage_of_noTie`（仮定ゼロ）',
            '(β) タイあり ∧ `TieFree` ⟹ `liftTie_case_tieFree`',
            '**(δ) タイ ∧ ¬`TieFree` ∧ 行 2 に非零 ＝ 本当の残核**']
    print('### 排他的な 4+1 分割（上の優先順で振り分け）')
    print()
    print('| 場合 | ' + ' | '.join('`|R|`=%d' % L for L in (2, 3, 4, 5)) + ' |')
    print('|---|' + '--:|' * 4)
    for k in keys:
        print('| %s | %s |' % (k, ' | '.join(
            '%d (%.1f%%)' % (rows[L][k], 100.0 * rows[L][k] /
                             max(sum(rows[L].values()), 1))
            for L in (2, 3, 4, 5))))
    print('| **分母** | %s |' % ' | '.join(
        '**%d**' % sum(rows[L].values()) for L in (2, 3, 4, 5)))
    print()
    print('### 生の該当（排他化しない。重複あり）')
    print()
    print('| 条件 | ' + ' | '.join('`|R|`=%d' % L for L in (2, 3, 4, 5)) + ' |')
    print('|---|' + '--:|' * 4)
    for k in ['ブロッカー無し', '行 2 ≡ 0', 'タイ無し', '`1<=v` ∧ `TieFree`',
              '**合計**']:
        print('| %s | %s |' % (k, ' | '.join(
            '%d' % rawagg[L][k] for L in (2, 3, 4, 5))))
    print()


if __name__ == '__main__':
    main()
