# -*- coding: utf-8 -*-
"""**R114 の続き（先回り）—— L3 の「結論側の節 3 で作る」線が使えるかを測る。**

⚠ 文は `L105Cap.lean:4481 / 4595` から写した（教訓: 前提も除外条件も写す）:

    `LiftTieCoreZero` : `argOK R` ∧ **`∃ p ∈ R, p.2.1 = 0`** ∧ `(0,0,0)::R ∈ W 0`
                        ⟹ `Lift1 ((0,0,0)::R) 1 ∈ W 2`
    `LiftTieCoreOne`  : 同（`z=1`）。前提の段 **1**、結論の段 **3**

`Aop`（`Wset.lean:169`）の節 3 は **`∃ m, m < u ∧ domT M m ∧ …`**。
⟹ 結論（段 `u = 2` / `3`）で節 3 を使うには **`∃ m < u, domT Y m`**（`Y := Lift1 X 1`）が要る。
`domT Y m` = **`lev Y (|Y|-1) = m+1`** ∧ **`¬ hasParent Y (srow Y (|Y|-1)) (|Y|-1)`**。
⟹ **`m < u` ⟺ `lev Y (|Y|-1) <= u`**（`u=2` なら `lev <= 2`、`u=3` なら `lev <= 3`）。

★ **測る前に書く予想**: `Y` の最終列は `X` の最終列の行 1 を（錐なら）`+1` したもの。
   `lev` が 2 以下に収まるのは**最終列の行 1 が 0 か 1 のときだけ**なので、**大半は外れるはず**。
   ⟹ **節 3 は結論側でもほとんど使えない**のではないか。**反例の形＝「`lev <= u` かつ孤児」。**

**箱**（2 つ。行 2 の軸を振る）:
  (a) 列 行0∈[1,2]×行1∈[0,2]×**行2∈[0,1]**
  (b) 列 行0∈[1,3]×行1∈[0,3]×**行2∈[0,2]**
**母集団**: `argOK R` ∧ `∃p ∈ R, p.2.1 = 0`（`v=0` なので `¬(1<=v ∧ TieFree)` は自動）。
⚠ `X ∈ W (2v+z)` は有限で判定できない（R94）ので落とした**上位集合**。
**単位**: 事例。`|R|` <= 4 は全数、それ以上は標本。**所属の判定はしない。**
"""
import sys, itertools, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter


def lev(c):
    return 2 * c[1] + c[2]


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def Lift1(X, d):
    return [(c[0], c[1] + (d if trio.is_ancestor(X, 1, 0, i) else 0), c[2])
            for i, c in enumerate(X)]


def run(COL, Ls, label):
    c = Counter(); ex = {}
    for L in Ls:
        for Rt in itertools.product(COL, repeat=L):
            R = list(Rt)
            if any(p[0] < 1 for p in R):
                continue
            if not any(p[1] == 0 for p in R):
                continue                              # タイ（v=0）
            for z in (0, 1):
                X = [(0, 0, z)] + R
                Y = Lift1(X, 1)
                u = 2 + z                             # 結論の段（2v+z+2, v=0）
                jY = len(Y) - 1
                c[(f'z={z}', '分母')] += 1
                lv = lev(Y[jY])
                orph = trio.parent(Y, srow(Y, jY), jY) is None
                c[(f'z={z}', f'lev(Y の最終列) <= {u}' if lv <= u
                   else f'lev(Y の最終列) > {u}')] += 1
                c[(f'z={z}', '最終列が孤児' if orph else '最終列に親がある')] += 1
                ok = (lv <= u) and orph
                c[(f'z={z}', '★ 節 3 が使える（lev<=u ∧ 孤児）' if ok
                   else '節 3 は使えない')] += 1
                if ok:
                    ex.setdefault(f'z={z} 節 3 が使える例', (R, z, Y, lv, u))
                # 参考: 前提側 X の段 2v+z = z で節 3 が使えるか（m < z）
                c[(f'z={z}', f'前提側: 節 3 は m<{z} を要求 ⟹ ' +
                   ('**常に不可**' if z == 0 else 'm=0 のみ可'))] += 1
                # `srow_Lift1_last` の検算（緑）
                c[(f'z={z}', 'srow_Lift1_last 検算/' +
                   ('ok' if srow(Y, jY) == srow(X, len(X) - 1) else '**不一致**'))] += 1
    print(f'### {label}')
    for zz in ('z=0', 'z=1'):
        sub = {k[1]: n for k, n in c.items() if k[0] == zz}
        if not sub:
            continue
        den = sub.get('分母', 1)
        print(f'  -- {zz}（分母 {den}） --')
        for k in sorted(sub, key=str):
            if k == '分母':
                continue
            print(f'     {k:44s} {sub[k]:9d}  ({100*sub[k]/den:5.2f}%)')
    for k in sorted(ex):
        print(f'  ★ {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    Ls = tuple(range(1, a.L + 1))
    run([(d, b, c) for d in (1, 2) for b in (0, 1, 2) for c in (0, 1)], Ls,
        f'R118 (a) 箱 行2<=1／`v=0`／|R|<={a.L}／全数')
    run([(d, b, c) for d in (1, 2, 3) for b in (0, 1, 2, 3) for c in (0, 1, 2)],
        (1, 2, 3), 'R118 (b) 箱 **行2<=2**／`v=0`／|R|<=3／全数')
