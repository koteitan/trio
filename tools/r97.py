# -*- coding: utf-8 -*-
"""**課題 R97（team-lead は「R94」と呼んだが §R94 と衝突するので改番）—— タイの本数。**

L3 が `LiftTieSelf` の証明で `L53.split_lastTie`（`L53Subst.lean:1692`）を使う。
その形は「**最後のタイを剥がすと残りは無タイ**」:

    (∃ p ∈ R, p.2.1 = v) ⟹ ∃ R₁ tie R₂, R = R₁ ++ [tie] ++ R₂ ∧ tie.2.1 = v
                             ∧ (∀ p ∈ R₂, p.2.1 ≠ v)

⟹ **タイが常に 1 本なら `split_lastTie` が一撃で効く。** 何本かを測る。

母集団（教訓 19/20: **定理が見る形だけ**）—— `TowerOK2` が実際に呼ばれる場面:

    `argOK R`（`Wset:1314`）           R の全列が行 0 >= 1
    `R ≠ []`
    `z <= 1`
    `domT R m`（`Wset:61`）            `lev R (|R|-1) = m+1` ∧ `¬ hasParent R (srow …) (|R|-1)`
    `srow R (|R|-1) = 2`（`Trio:81`）  最終列の行 2 > 0
    `hasParent ((0,v,z) :: R) 2 |R|`   **根が孤児を復活させる**
    ⟹ `L53.tower2_zr`（`:2380`、緑）より **`z < c`** が自動（`c = entry R 2 (|R|-1)`）

⚠ team-lead の指示「母集団を `z < c` に絞れ」は、上の 6 条件を課せば**自動で満たされる**。
別に絞るのではなく、`z < c` が出ることを**検算**する（出なければ定義の読み違い ⟹ 即報告）。

分類（`Final.lean:145-155` の H11 実測と同じ 4 分類）:

    狭義 `Strict v R`（`L53Subst:2099`） = `∀ p ∈ R, v < p.2.1`     … 仮定ゼロで済む
    無タイ `NoTie v R`（`:2235`）        = `∀ p ∈ R, p.2.1 ≠ v`     … 仮定ゼロで済む
    タイ（`∃ p ∈ R, p.2.1 = v`）                                    … ここが核
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter


def lev(c):
    return 2 * c[1] + c[2]


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def has_parent(S, i, j):
    return trio.parent(S, i, j) is not None


def scene(R, v, z):
    """`TowerOK2` が呼ばれる場面か。満たすなら (m, c) を返す。"""
    if not R or any(p[0] < 1 for p in R):
        return None                              # argOK
    if z > 1:
        return None
    j = len(R) - 1
    if srow(R, j) != 2:
        return None                              # srow R (|R|-1) = 2
    if has_parent(R, 2, j):
        return None                              # domT の第 2 条件 ¬hasParent
    m = lev(R[j]) - 1
    if m < 0:
        return None                              # domT の第 1 条件 lev = m+1
    S = [(0, v, z)] + R
    if not has_parent(S, 2, len(S) - 1):
        return None                              # 根が孤児を復活させる
    return (m, R[j][2])


def run(DS, BS, CS, VS, ZS, LS, label):
    COL = [(d, b, c) for d in DS for b in BS for c in CS]
    n_scene = 0
    ties = Counter(); cls = Counter(); zc = Counter()
    tie_after = Counter(); tie_pos = Counter()
    ex = {}
    t0 = time.time()
    for L in LS:
        for Rt in itertools.product(COL, repeat=L):
            R = list(Rt)
            for v in VS:
                for z in ZS:
                    sc = scene(R, v, z)
                    if sc is None:
                        continue
                    m, c = sc
                    n_scene += 1
                    zc['z < c' if z < c else '**z >= c（定義の読み違い）**'] += 1
                    if z >= c:
                        ex.setdefault('z>=c', (R, v, z, m, c))
                    k = sum(1 for p in R if p[1] == v)
                    ties[k] += 1
                    ties[('|R|', L, k)] += 1
                    if R[-1][1] == v:
                        cls['**最終列がタイ**'] += 1
                        ex.setdefault('最終列がタイ', (R, v, z))
                    if all(v < p[1] for p in R):
                        cls['狭義 Strict'] += 1
                    elif all(p[1] != v for p in R):
                        cls['無タイ（狭義でない）'] += 1
                    else:
                        cls['タイ ← 核'] += 1
                        # split_lastTie: 最後のタイを剥がしたあと R2 は無タイ（定理。検算）
                        idx = max(i for i, p in enumerate(R) if p[1] == v)
                        tie_pos['最後 (|R|-1)' if idx == len(R) - 1
                                else f'末尾から {len(R)-1-idx}'] += 1
                        R1 = R[:idx]
                        tie_after[f'R1 に残るタイ {sum(1 for p in R1 if p[1] == v)} 本'] += 1
                        if k >= 2:
                            ex.setdefault('タイ 2 本以上', (R, v, z, k))
    dt = time.time() - t0
    print(f'### {label}  ({dt:.1f}s)  `TowerOK2` の場面 **{n_scene}** 件')
    if n_scene == 0:
        print('  ⚠ 場面が 0 件。母集団の作り方を疑うこと（教訓 11）'); return
    print('  -- 検算: `tower2_zr` の `z < c` --')
    for k in sorted(zc):
        print(f'     {k:28s} {zc[k]:9d}')
    print('  -- (t4) H11 の 4 分類の再現 --')
    for k in sorted(cls):
        print(f'     {k:22s} {cls[k]:9d}  ({100*cls[k]/n_scene:5.1f}%)')
    print('  -- (t1) ★ タイの本数の分布 --')
    tot_tie = sum(n for kk, n in ties.items() if isinstance(kk, int) and kk >= 1)
    for k in sorted(x for x in ties if isinstance(x, int)):
        pct = f'  ({100*ties[k]/tot_tie:5.1f}% of タイ)' if k >= 1 and tot_tie else ''
        print(f'     タイ {k} 本 : {ties[k]:9d}{pct}')
    print('     -- |R| 別（最大本数が |R| とともに増えるか） --')
    for k in sorted(x for x in ties if isinstance(x, tuple)):
        print(f'       |R|={k[1]}  タイ {k[2]} 本 : {ties[k]:9d}')
    print('  -- (t3) 最後のタイの位置 / 剥がしたあと R1 に残るタイ --')
    for k in sorted(tie_pos):
        print(f'     {k:22s} {tie_pos[k]:9d}')
    for k in sorted(tie_after):
        print(f'     {k:22s} {tie_after[k]:9d}')
    for k in sorted(ex):
        print(f'  ex {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    run((1, 2, 3), (0, 1, 2, 3), (0, 1, 2), (0, 1, 2, 3), (0, 1),
        tuple(range(1, a.L + 1)), f'R97 タイの本数 |R|<={a.L}（列 3x4x3=36）')
