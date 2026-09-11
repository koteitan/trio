# 壁

シート行376 `(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,3,0)`。

## いま開いている最小の行列（bms で実測）

    R375m (6,1,0) = (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,2,0)(6,1,0)
    標準形。展開は TwD 6 R375m (n+1)（R375m 自身の縦塔）。

木では `bdA [2,0]`（幅 2 のブロックの上に裸の 1 の枠）を台座 `R341` の上に置いたもの。

## 壁の還元（全部緑・族を使わない）

    FLr []        = nil
    FLr (B :: Bs) = two (FLr Bs) (pay nil B)        平らな荷の鎖（頭が右端）
    PFL Bs        = GOK (one nil (two nil (FLr Bs)))

    FLnilStep := ∀ Bs (全部 Bok), PFL Bs → PFL ([] :: Bs)      ← いちばん弱い形
    PFLtow    := ∀ Bs, ∀ n, GOK (UtwP [nil] (FLr Bs) n)        ← 十分条件

    PFLtow → FLnilStep → Pay2 → hang6_R375m → R375m (6,1,0) ∈ W 0

    Pay2 := ∀ B, Bok B → GOK (one nil (two nil (two nil (pay nil B))))

緑の部品:

    twoIt_FLr / JkT_PFL / PFL_rep / PFL_dup / PFL_cons / Pay2_of_FLnilStep
    PFL_single_nil（`Bs = []` の場合は無条件で緑）
    FLnilStep_of_PFLtow / R375m61_of_PFLtow
    GOK_flat2 / GOK_FLr_rep_nil（荷が全部空の鎖は緑）
    WPd_FLr（平らな鎖は**枠の位置**なら緑。2 の枠の直下＝走りだけが壁）
    W0_acc（荷の展開 1 手は `W 0` の上で整礎）

## 入れ子帰納法（荷の W 帰納 × 鎖のリスト）

`PFL_cons` の中身。右端の荷 `B` について `A2'`:

- `B` に親あり → `GoodFb_snoc_innerJt0` → `PFL (B⟦n⟧ :: Bs)`（IH）
- `B = B₀ ++ [(0,0,0)]` → `GoodFb_snoc_dupJt0` の平らな鎖
  `twoIt (FLr Bs) (pay nil B₀) n = FLr (replicate n B₀ ++ Bs)` → IH（`B₀` は小さい）
- **`B = []`** → 階段になる。ここだけ残っている（= `FLnilStep`）。

## 残り 1 手の中身

`PFL ([] :: Bs)` の展開は階段で、悪い部分は `PFL Bs` のブロックまるごと
（bms 実測、シフト 2）。塔を追うと

    塔の上のブロックの右端の荷 → 空 → 鎖の長さ m が 1 減る → m = 0 で幅 1
    → その階段が幅 0 のブロックを作る → 幅 0 の展開は全体の縦塔（荷が要る）

で `FoneB`（幅 2 の上の幅 0）に戻る。円が閉じるかは
「ブロックごとの (荷の多重集合, 鎖の長さ)」の測度次第。

## 死んだ道（族）

族 `WPd` / `WFd` / `WGd` は構造的に塞がっている。
**階段は塔を「予算 1 下げ・幅 1 下げ」で積み、鎖は兄弟を開いて「幅だけ 1 上げ」る。**
鎖は幅の余裕を 1 消費するのに補充できないので、兄弟条件の下限で必ず割れる。
`lo(i)` を兄弟条件の下限、`f(w)` を幅 `w` の空木に要る予算とすると
`f(i+1) ≤ lo(i)`（鎖）と `f(i+1) = lo(i)+1`（階段）で矛盾。
詳細は notes 追記282〜287。
