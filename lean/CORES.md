# 核の一覧 —— `Final.lean` の「あと 1 本」を大きさで並べた表

作成 2026-08-30（R1、課題 R88）。**明日の最初の一手はこの表を見ることから。**

## ⚠ この表の読み方（先に読むこと）

**量化子や前提の個数は「証明のしやすさ」の代理指標にすぎない。**
実体ではない。2026-08-29 だけで、代理指標を実体と取り違えた転びが 6 回あった:

    「短い文ほど証明しやすい」→ **`WSnoc`（3 量化）は循環、`WCat` は残核より広い**
    「族形は界面を落とす」  → **v0.118.52 で同語反復と判明**（`GRAFTALL-PLAN 1.9.42`）
    「1 列だから小さい」    → **`CoreSingleton` の `GX` は `∀M ∀vz ∀i ∀at` を隠している**

**⟹ この表は「比べ忘れないための一覧」であって、順位表ではない。**
判断は必ず**定義を開いて**行うこと。

## 表（`TRIO_terminates_of_*` の仮定を全部）

`∀` = 量化子の数、`→` = 前提の数（定義本体を数えた機械カウント）。
**`GX` 込み**の列は `GX`（`Gamma.lean:169`）を展開した実効値（`+7 量化 / +5 前提`）。

| 命題 | 場所 | ∀ | → | GX 込み | 主語 | 段 | 経路 | より強いもの（＝ここから出る） | 状態 |
|---|---|---|---|---|---|---|---|---|---|
| **`CoreSingleton`** | `L53Subst:4183` | 2 | 0 | **9 / 5** | **1 列** | - | C | `CoreCap`, (2 文脈核) | **極小・単独** |
| **`CoreCap`** | `Lind:176` | 7 | 5 | 7 / 5 | 1 ブロックの末尾差し替え | - | C | - | **極小・単独・`GX` 無し** |
| **`TowerOK`** | `L53Subst:1086` | 3 | 7 | 3 / 7 | `(0,v,z) :: R` の展開 | m/u | D | `TowerGraft2 ∧ TowerExp`, `TowerOK1 ∧ TowerOK2` | **極小・単独** |
| `TowerOK2` | `L53Subst:1122` | 3 | 8 | 3 / 8 | 同上（`srow=2`） | m/u | D | - | `TowerOK1` は節 3 でのみ既済（§R83） |
| `CoreCtxSuffixLift` | `Gamma:1278` | 4 | 8 | 11 / 13 | 文脈の接尾辞 | - | C | `CoreSingleton` | 対で使う |
| `CorePlantCtxLift` | `Gamma:723` | 3 | 4 | 10 / 9 | 文脈の plant | - | C | `CoreSingleton` | 対で使う |
| `Row0Free` | `Wtower2:262` | 3 | 4 | 3 / 4 | 行 1・行 2 が同じ 2 本 | - | — | - | **⚠ 強すぎ**（`mem_W_of_row0free` が全部出す） |
| **`WCat`** | `Wtower2:1974` | 3 | 2 | 3 / 2 | `A ++ B` | - | B | `WSnoc` | **文は最小だが残核より広い**（§R42） |
| `WSnoc` | `L53Subst:3416` | 1 | 3 | 1 / 3 | `C ++ [p]` | m/u | B | - | 循環（§R29-5）。`LiftStage` も出す |
| `Subst1gReviveSelf` | `Wtower2:3274` | 3 | 10 | 3 / 10 | 置換 | - | A | - | 半年の残核 |
| `Subst1gRevive` | `Wtower2:3251` | 2 | 8 | 2 / 8 | 置換 | m/u | A | `Subst1gReviveSelf` | |
| `Subst1g` | `Wtower2:2720` | 2 | 8 | 2 / 8 | 置換 | m/u | A | `Subst1gRevive` | |
| `Subst1` | `Wtower2:2656` | 3 | 8 | 3 / 8 | 置換 | m/u | A | `Subst1g` | 相方に `WCat` |
| `SubstClosed` | `Wtower2:2623` | 8 | 14 | 8 / 14 | 置換閉包 | m/u | A | `Subst1`, `SubstClosedG` | 相方に `WCat` |
| `ShiftTowerClosedS` | `Wtower2:1771` | 2 | 4 | 2 / 4 | `shTower` | m/u | A/B | `WCat`, `SubstClosedG` | 相方に `TowerExp` |
| `LiftStageParented` | `Wtower2:551` | 3 | 5 | 3 / 5 | | m/u | A | `ShiftTowerClosedS` | 相方に `TowerExp` |
| `LiftStage` | `Wtower2:36` | 1 | 1 | 1 / 1 | | m/u | A | 上の全部, `WSnoc`, `Row1Mono`, `WConvex`, `TieFree` … | **文は小さいが上流が多い** |
| `TowerGraft2` | `Wset:4498` | 3 | 10 | 3 / 10 | | m/u | A | `LiftStage` | `TowerOK` の片割れ |
| `TowerExp` | `Wset:4507` | 3 | 9 | 3 / 9 | | m/u | A/B | `TowerExp1 ∧ TowerExp2`, `WSnoc`, `WCat`, `SubstClosedG` | `TowerOK` の片割れ |
| `TowerExp2` | `Wtower2:1859` | 3 | 10 | 3 / 10 | `srow=2` | m/u | A | `TowerExp2Root` | |
| `TowerExp2Low` | `Wtower2:2247` | 3 | 11 | 3 / 11 | | m/u | A | `TowerExp2Root` | |
| `TowerExp2Root` | `Wtower2:2257` | 3 | 11 | 3 / 11 | | - | A | `SubstClosed ∧ LiftStage` | |
| `Row1Mono` | `Wtower2:151` | 4 | 5 | 4 / 5 | | - | A | `Row1DownLocal`, `Row1DownRoot0` | 相方に `TowerExp` |
| `Row1DownLocal` | `L53Subst:2574` | 1 | 2 | 1 / 2 | | - | A | - | `Row1Mono` より弱い |
| `Row1DownRoot0` | `L53Subst:2579` | 1 | 2 | 1 / 2 | | - | A | - | 同上 |
| `WConvex` | `Wtower2:450` | 1 | 4 | 1 / 4 | | - | A | - | 相方に `TowerExp` |
| `LiftTie` | `L53Subst:2337` | 2 | 3 | 2 / 3 | | m/u | D | `MliftR` | `TowerGraft2` 側 |
| `MliftR` | `L53Subst:2765` | 1 | 1 | 1 / 1 | | m/u | D | - | |
| `GraftFromExp` | `L53Subst:2644` | 3 | 6 | 3 / 6 | `graft R y` | m/u | D | `Subst1gRevive ∧ WSnoc` | §R76: 側条件は場面で自動 |

## ⛔ 偽・空虚と判明したもの（**二度と候補に挙げない**）

| 命題 | 判定 | 根拠 |
|---|---|---|
| **`InfEquip`** | **偽** | `Infcex.not_infEquip`。反例 `M = [(1,0,2),(2,0,0)]`。結論の `entry M 2 p ≤ 1` が `argOK` からも `CtxOK` からも出ない（v0.118.56） |
| **`TieFree`** | **構文的不変量にならない** | `L10Tie.lean:35`。`Wstar` は `∀ v` を走るので `v` が `R` の行 1 の値とぶつかった瞬間にタイ。R1 の §R72-d で**適用 20347 回すべてでタイる `v` が存在**と実測 |
| **`AminROper`** | **偽** | SESSION §101 |
| **`WConvex1`** | 3 本目ではない | SESSION §114。`LiftStage` への別経路にすぎない |
| `Row0Free` | ⚠ 強すぎ | `Wtower2.lean:269` の docstring:「これを仮定すると**すべての**列が `Wself` に入ってしまう」 |
| （族形 3 本） | **同語反復** | v0.118.52。`CoreGpowPeel` / `tower1_mem2_fam` / `tower1_mem2_gpow` は**言い換えであって還元ではない** |

## ★ 極小元（他のどの核からも出ない＝いちばん弱い）＝ **狙うべき候補**

    **`CoreCap`**       … 単独で足りる。**`GX` を含まない純 `W` の 1 文**。7 量化 / 5 前提
    **`CoreSingleton`** … 単独で足りる。主語は 1 列だが `GX` 込みで実効 9 量化 / 5 前提
    **`TowerOK`**       … 単独で足りる。3 量化 / 7 前提。`TowerOK1`（節 3 側のみ既済）＋ `TowerOK2`
    `MliftR` / `Row1DownLocal` / `Row1DownRoot0` / `WConvex` … 経路 A の末端だが**相方が要る**

**到達点はどれも同じ**（R1 の §R87: ブック全 7 シート 20415 行 ＋ `D_1..D_12`)。
⟹ **証明しやすいものを選んでよい。**

## 参考: 単独で足りるか / 相方が要るか

    **単独**: `TowerOK` / `Row0Free`(⚠) / `Subst1g` / `Subst1gRevive` / `Subst1gReviveSelf`
             / `WSnoc` / `CoreSingleton` / `CoreCap`
    **相方（`TowerExp` 系）が要る**: `TowerGraft2` / `LiftStage` / `Row1Mono` / `WConvex`
             / `LiftStageParented` / `ShiftTowerClosedS` / `WCat` / `SubstClosed` / `Subst1`

## 出典

R1 の測定・読解: `tools/dbms/R1-NOTES.md` の §R71-a（含意地図 22 本）、§R73（`TowerExp`）、
§R83（`TowerOK1` は節 3 の与件を要求）、§R86（`Gamma` の履歴）、§R87（両路線の合流）。
