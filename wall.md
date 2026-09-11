# 壁

シート行376 `(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,3,0)`。

## いま開いている最小の行列（bms で実測）

    R375m (6,1,0) = (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,2,0)(6,1,0)
    標準形。展開は TwD 6 R375m (n+1)（R375m 自身の縦塔）。

木では `bdA [2,0]`（幅 2 のブロックの上に裸の 1 の枠）を台座 `R341` の上に置いたもの。

## いちばん的を絞った壁（1 文、`WPd` 層）

    bdA (j :: js)  = one nil (stkP j (bdA js))
    stkP 0 X = X,  stkP (q+1) X = two nil (stkP q X)

    RunP2 := ∀ j k ks X, JkA X → (∀ ks', WPd ks' X) → j ≤ k →
               WPd ((k+1) :: ks) (stkP j X)

    RunP2 → WPd_bdA_all / WPd_bdAC_all（幅の制限なし）
          → Pay2 → R375m (6,1,0) ∈ W 0
          → ∀n GOK (bdA (replicate n 2)) → R375m (6,2,0) ∈ W 0

**`j = 1`, `X = nil` はちょうど既存の `WPd_run`（緑）。** `RunP2` はそれを
「`X = nil` → どこでも良い `X`」「`j = 1` → 一般の `j`」に広げたもの。
`WPd_bdA_le1`（幅 ≤ 1）が通っていたのは `j = 1` のとき `stkP 0 X = X` で
2 の枠の直上に走りが来なかったから。**幅 2 で初めて `stkP 1` が来る。**

`bdA` に絞ると

    RunBdA := ∀ j k ks js, 1 ≤ j → j ≤ k → (∀ ks', WPd ks' (bdA js)) →
                WPd ((k+1) :: ks) (stkP j (bdA js))
    RunBdA → R375m (6,2,0) ∈ W 0

まで弱められ、いちばん小さい未証明は

    StkBlk2 := ∀ k ks, 2 ≤ k → WPd ((k+1) :: ks) (stk 2)

    WPd_stk2 : WPd (0 :: ks) (stk 2)            ★緑（1 の枠の直上）
    WPd_run  : 1 ≤ k → WPd ((k+1)::ks) (stk 1)  ★緑（2 の枠の直上、長さ 1）

`StkBlk2` を開くと `two N (stk 2) = RunS ([N, nil] ++ [nil])` で
`GOK_oneUV_RunSB ctx0 [N, nil] nil V` に嵌まる。階段の塔は 1 段ごとに
`[fone ·, ftwo N, ftwo nil]` の **3 枠**伸びる。`WCtx` は 2 の枠が連続する
文脈を持てないのでここで詰まる。`HGx` なら持てるので、`GNilO` から出る見込み。

## 2 つの道は同じ壁（緑）

    WPd_of_GOKall : GOKall → ∀ ks Z, FrmN ks Z → WPd ks Z
    R375m61_of_GOKall / R375m62_of_GOKall / R375m62_of_APzAll

`GOKall := ∀ T, JkT T → GOK T` から `WPd` 層は全部出る（`WPd_iff` + `WCtx_JkT`）。
だから `bdA` 経由（`RunBdA` / `StkBlk2`）と裸の記録経由（`GNilO` / `APz…`）は
同じ壁の別の言い方。開いている 2 つの行列はどちらからでも出る。

## 一般の停止性としての壁（文脈なしの 4 文）

    APz M   := ∀ U, JkT U → GOK U → GOK (one U M)
    APzO2 W := ∀ M, JkA M → APz M → APz (one M W)
    APzT2 W := ∀ M, JkA M → APz M → APz (two M W)

    APzO2One := ∀ Z T, JkA Z → JkA T → APzO2 Z → APzO2 T → APzO2 (one Z T)
    APzO2Two := ∀ Z T, JkA Z → JkA T → APzO2 Z → APzO2 T → APzO2 (two Z T)
    APzT2One := ∀ Z T, JkA Z → JkA T → APzT2 Z → APzT2 T → APzT2 (one Z T)
    APzT2Two := ∀ Z T, JkA Z → JkA T → APzT2 Z → APzT2 T → APzT2 (two Z T)

    R375m61_of_APz4 : 4 つから R375m (6,1,0) ∈ W 0

どれも「記録の直上にまた記録がある」形。語で見ると `(l+1,r,0) … (l+2,r',0)` で
高さが 1 ずつ上がる列、つまり塔。

## 同値な言い方

    APzAll := ∀ M, JkA M → APz M
    GOKall := ∀ T, JkT T → GOK T                （= この符号化での z<2 の停止性）
    GAll   := ∀ F, HGx F → ∀ Z, JkA Z → GOK (plug F Z)
    GNilO  := ∀ D, HGx D → OSib D nil     GNilT := ∀ D, HGx D → TSib D nil

    APzAll ⟺ GOKall,  GAll ⟺ GNilO ∧ GNilT ∧ 底,  GOKall → GAll

## 緑になっている還元

    GOKall_of_APzAll : 木の構造帰納。TopOk があるので `two` は字の先頭段に来られず、
                       nil（GOK_nil）/ pay（AY0）/ one（APz を U = N に当てる）の 3 つ
    APzAll_of_steps  : APzOne ∧ APzTwo → APzAll
    APzO2_nil        : 無条件で緑（APz_oneNil ← GOK_oneOneNil）
    APzO2_pay        : 荷の W 帰納（dupJs0 / innerJs0、鎖は itJ）
    APzT2_pay        : 荷の W 帰納（dupJt0 / innerJt0、鎖は twoIt）
    APz_twoNil       : APzT2 nil ⟸ APzOne（two V nil = RunS [V] の階段、塔は APzOne）
    APzO2_oneNil     : APzO2 (one Z nil) ⟸ APzO2 Z
    APzT2_oneNil     : APzT2 (one Z nil) ⟸ APzT2 Z
    GSib_tree / SelfW_HGx / hangG_fone / hangG_ftwo / GNilO_fone / GNilO_ftwo / GNilT_fone
    PS_cons / PZ_cons / PS_consF / TSibF_pay
    QFL_cons / QFL_all / Pay2_of_QFL0 / TowHCx / QH0
    GOK_oneUV_RunSB（階段）/ APnil_gen0（裸の 1 の記録）/ W0_acc

## 測度（未解決）

4 文はどれも「記録を 1 枚剥がして深さ 1 の文脈へ」進む。`T = nil` なら
`APnil_gen0` で閉じる（緑）。`T ≠ nil` だと文脈が深くなり、荷のところで
文脈が 1 縮んで木が任意に戻る。`（木の大きさ, 文脈の長さ）`のどちらの
辞書式順序でも割れる。

## 死んだ道（族）

族 `WPd` / `WFd` / `WGd` は構造的に塞がっている。
**階段は塔を「予算 1 下げ・幅 1 下げ」で積み、鎖は兄弟を開いて「幅だけ 1 上げ」る。**
鎖は幅の余裕を 1 消費するのに補充できないので、兄弟条件の下限で必ず割れる。
詳細は notes 追記282〜287。
