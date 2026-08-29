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
| **`CoreCap`** | `Lind:176` | 7 | 5 | 7 / 5 | 1 ブロックの末尾差し替え | - | C | - | **極小・単独・`GX` 無し**。**R89: 展開は 3 分岐に尽き `WCat` を要求しない。残債務は `TowerOK2` の 1 点**（`R2-NOTES.md` §R89, commit `592fd26`。`c>=2` は L109 で穴でないと判明） |
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

## R89（R2, 2026-08-30）: `CoreCap` の展開の形を測った —— `WCat` は要らない

根拠: `R2-NOTES.md` §R89、commit `bc72e75` / `db140b2`。
プログラム `tools/dbms/r89.py` `r89b.py` `r89c.py` `r89d.py` `r89e.py` `r89ctl.py` `r89f.py`。

`CoreCap` が見る形 `S = Lift1 ((0,v,z) :: cap M b c) t` の展開は **3 分岐で尽きる**。
`|M|<=4` の**全数 24,008,400 件** ＋ `|M|∈{4,5,6}` のランダム標本 1,944,000 件で
**破れ 0**、陰性対照（式を壊すと 100% VIOL）つき。

| 分岐 | 割合(|M|<=4) | 展開の形 | Lean の等式 | 状態 |
|---|---|---|---|---|
| `noparent` | 44.0% | `S⟦n⟧ = S.dropLast` ＝ `CtxOK` の接頭辞 | `oper_eq_pred_of_noParent` | **無条件で閉** |
| `j0 >= 1` | 28.3% | `S⟦n⟧ = (0,v,z) :: R⟦n⟧` | `oper_cons_nat`（`Wset:2041`） | **無条件で閉** |
| `j0 = 0`, `srow=0` | — | `d0=d1=0` の反復 | `W_flatMap_copies`（`Wset:2551`）＋ `rsum_self_cons`（`:2539`） | **無条件で閉** |
| `j0 = 0`, `srow=1` | — | 塔 `tow v z R n` | `oper_cons_tower1`（`Wset:2789`） | `TowerOK1`（節 3 の与件がある場面でのみ既済、§R83） |
| **`j0 = 0`, `srow=2`** | — | `(0,v,z) :: graft R (Lift1 (M⟦n⟧) D1)` | `oper_cons_tower2`（`Wset:3231`） | **`TowerOK2` ＝ 残核** |

⟹ **`A ++ B`（独立な 2 つの `W` 元の連結 ＝ `WCat` 形）は `CoreCap` の展開に現れない。**
§131 の「塔 ⟹ `rsum` が破れる ⟹ `WCat` が要る」は **`WSnoc` 路線の話**で `CoreCap` には移らない:

    WSnoc   shTower Q e (n+1) = shTower Q e n ++ shiftr01 (n*e) 0 Q   ← 連結。rsum が要る
    CoreCap tow v z R (k+1)   = (0,v,z) :: graft R (tow v z R k)      ← graft。W_add を通らない

### R89 で分かった注意点（他の核の判定にも効く）

1. **`CtxOK` は母集団を絞らない。** 37,044 個の `(M,v,z)` すべてが装備ずみ
   （確定 30,348 / 予算切れ 6,696 / **確定した非装備 0**）。`tools/probe_cap2.py` の
   `ctx/not-equipped = 0` とも一致。⟹ 「`CtxOK` があるから悪い `M` は来ない」は言えない
2. **`argOK` は展開の木の下で破れる**（訪問 1,705,886 ノードの 5.6%）。起点は
   **`srow=0` の塔だけ**（他の分岐は `ok->VIOL` がゼロ）。そこは `W_flatMap_copies` で閉じている
3. ~~`CoreCap` は `∀ c : ℕ` なので `c >= 2` で `srow=2 & z=1` が起きる~~
   **⚠ 訂正（L3 の L109、commit `ab41f4e`）: これは穴ではなかった。**
   `srow=2 & z=1` が起きる（R2 実測 69,876 件）のは事実だが、生きている鎖
   `towerOK2_of_clause3`（`L53Subst:2432`）は `tower2_zr`（`:2380`）と
   `tower2_stage_fits'`（`:2406`）を使っており **`c` について一般**。
   `tower2_root_z_zero`（`:1473`）は `tower2_z_zero_of_parent`（`:1486`）からしか
   呼ばれず、そちらはどこからも呼ばれていない（死んだコード。R2 が `grep` で確認）
4. `j0` は `n` に依存しない（`Trio.lean:98`）。`b, c` には依存する（二分が反転するのが 15.2%）
