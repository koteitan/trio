# 壁

シート行376 `(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,3,0)`。

## いま開いている最小の行列（bms で実測）

    R375m (6,1,0) = (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,2,0)(6,1,0)
    R375m (6,2,0) も同じ壁から出る。

## 壁は 2 文（族 `ECtx` / `EOk`、`Rq` も予算も無い）

文脈の形を `(k, ks)` で持つ。内側から「1 の枠 `k` 枚」「2 の枠」
「1 の枠 `ks.head` 枚」「2 の枠」…、一番外は `fone V`（`JkT V`、`GOK V`）。

    ECtx 0 []        D := ∃ V, D = [fone V] ∧ JkT V ∧ GOK V
    ECtx (k+1) ks    D := D = D' ++ [fone U] ∧ ECtx k ks D' ∧ JkA U ∧ EOk k ks U
    ECtx 0 (k'::ks)  D := D = D' ++ [ftwo N] ∧ ECtx k' ks D' ∧ JkA N ∧ ∀ j, EOk j ks N
    EOk k ks X := ∀ D, ECtx k ks D → GOK (plug D X)

停止性は `(ks.length, k)` の辞書式。2 の枠でリストが 1 短くなるので、その木の
条件を「梯子の深さ `j` について全称」にしても回る。

    EPayT   := ∀ k' ks Z, JkA Z → EOk 0 (k'::ks) Z →
                 ∀ B Bok, EOk 0 (k'::ks) (pay Z B)
    ERunNil := ∀ k' ks N, JkA N → (∀ j, EOk j (k'::ks) N) →
                 EOk 0 (k'::ks) (two N nil)

    EOk_all : EPayT → ERunNil → ∀ X, JkA X → ∀ k ks, EOk k ks X
    APzAll_of_E → GOKall → R375m (6,1,0) / (6,2,0) ∈ W 0

どちらも「木が 2 の記録の直上に来る場合」だけ。

## 緑になっている還元

    底 (0, [])      : `EOk 0 [] X ↔ APz X`（`EOk_base_APz`）
    荷 (k+1, ks)    : `PS_consE` / `EOk_pay`（鎖に `EOk` を持ち回る W 帰納）
    裸の 2 (k+1,ks) : `EOk_twoNil` / `EOk_twoNil_base`
    空木 (k+1, ks)  : `EOk_nil_fone`
    one / two       : `EOk_one` / `EOk_two`（`plug` の付け替えだけ、予算なし）
    `EOk_payAll` / `EOk_twoNilAll` / `EOk_nilAll` / `EOk_all`

## なぜ 2 の枠止まりだけ残るか

`EOk_twoNil`（1 の枠止まり）の塔は `(fone N)^m` で形が `(k+m, ks)` に伸びるだけ。
族の条件 `∀ j, EOk j ks N` でちょうど覆える。

走りの塔（`GOK_twoTwoNilW_gen` の `nstN2 N' N k`）は `[fone N, ftwo N']` を
1 段ずつ足すので、形が `(0, k'::ks) → (0, 1::k'::ks) → (0, 1::1::k'::ks) → …` と
**リストごと伸びる**。族が保証するのは `(·, ks)` の形だけなので届かない。

## 他の言い方（全部同値、緑の還元あり）

    APzAll ⟺ GOKall := ∀ T, JkT T → GOK T
      ⟺ GNilO ∧ GNilT ∧ 底（HGx 文脈）
      ⟸ APzO2One ∧ APzO2Two ∧ APzT2One ∧ APzT2Two（文脈なしの 4 文）
      ⟸ EPayT ∧ ERunNil（族 `ECtx`、いちばん細かい）

    GOKall → WPd 層全部 → RunP2 → RunBdA → bdA 全幅
    QL_all : 平らな鎖は `LOk` の梯子で無条件に良い（緑）

## 死んだ道（族）

`WPd` / `WFd` / `WGd` は予算が鎖の長さに追いつかない。
`APd` は `Rq (false::ks) U = TopOk U` が 2 頭の木を弾く。
`ECtx` はどちらも無いが、走りの塔が形のリストを伸ばすところが残っている。
詳細は notes 追記282〜287、301、309。
