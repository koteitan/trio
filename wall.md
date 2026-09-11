# 壁

シート行376 `(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,3,0)`。

## いま開いている最小の行列（bms で実測）

    R375m (6,1,0) = (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,2,0)(6,1,0)
    R375m (6,2,0) も同じ壁から出る。

## 壁は走り 1 文（族 `ECtx` / `EOk`、`Rq` も予算も無い）

文脈の形を `(k, ks)` で持つ。内側から「1 の枠 `k` 枚」「2 の枠」
「1 の枠 `ks.head` 枚」「2 の枠」…、一番外は `fone V`（`JkT V`、`GOK V`）。

    ECtx 0 []        D := ∃ V, D = [fone V] ∧ JkT V ∧ GOK V
    ECtx (k+1) ks    D := D = D' ++ [fone U] ∧ ECtx k ks D' ∧ JkA U ∧ EOk k ks U
    ECtx 0 (k'::ks)  D := D = D' ++ [ftwo N] ∧ ECtx k' ks D' ∧ JkA N ∧ EOk k' ks N
    EOk k ks X := ∀ D, ECtx k ks D → GOK (plug D X)

停止性は `(ks.length, k)` の辞書式。`Rq` も予算も無い。

    ERun := ∀ k' ks, EOk 0 (k' :: ks) nil       ★これ 1 本

    ENil_of_ERun → EAll_of_ENil → APzAll_of_ENil → GOKall
      → R375m (6,1,0) / (6,2,0) ∈ W 0

言葉で言うと「**空木が 2 の記録の直上で良い**」。語では 2 の記録が 2 つ続く走り。

## 緑になっている還元

    底 (0, [])      : `EOk 0 [] X ↔ APz X`（`EOk_base_APz`）/ `EOk_nil_base`
    荷 どの形でも   : `EOk_payA`（`PS_consE` / `PZ_consE` / `APz_pay`）
    空木 (k+1, ks)  : `EOk_nilF`（`APnil_gen0` + 荷）
    one / two       : `EOk_one` / `EOk_two`（`plug` の付け替えだけ、予算なし）
    `EAll_pay` / `EAll_of_ENil` / `ENil_of_ERun`

## 何が足りないか

`GOK_twoTwoNilW_gen` の階段 `nstN2 N' N k` は `[fone N, ftwo N']` を 1 段ずつ
足すので、形が `(0, k'::ks) → (0, 1::k'::ks) → …` と**リストごと伸びる**。
族の条件は `(·, ks)` の形しかくれない。

1 の枠の塔（`(fone N)^m`）は形が `(k+m, ks)` に伸びるだけなので、
`EOk_twoNil` が `∀ j, EOk j ks N` を**補題の仮定**で取れば覆える。
走りの塔だけ覆えない。

## 族の条件の強さのトレードオフ（2026-09-12 に実測）

2 の枠の側条件を `∀ j, EOk j ks N`（強い）にすると:
- `EOk_twoNil` が使えて `nil` at `(0, k'::ks)`（`k' ≥ 1`）が緑
- 代わりに `PZ_consE` が「∀ 形」の仮定を要求し、`EOk_nilF`（枠の木の荷）が届かない

1 つの形（弱い）にすると:
- `PZ_consE` も `EOk_nilF` も緑。壁は `ERun` 1 本にまとまる
- 代わりに `nil` at `(0, k'::ks)` が全部壁になる

両方取るには 1 の枠の条件も形で場合分けして強める必要がある
（`ECtx 1 (k''::ks'')` だけ `∀ j, EOk 0 (j::ks'') U`。停止性は
`(|ks''|+1, 0) < (|ks''|+1, 1)` で保たれる）。ただし `PS_consE` の鎖に
同じ強さが要るので、そこが次の検討点。

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
