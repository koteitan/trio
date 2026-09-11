# 壁

シート行376 `(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,3,0)`。

## いま開いている最小の行列（bms で実測）

    R375m (6,1,0) = (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,2,0)(6,1,0)
    標準形。展開は TwD 6 R375m (n+1)（R375m 自身の縦塔）。

木では `bdA [2,0]`（幅 2 のブロックの上に裸の 1 の枠）を台座 `R341` の上に置いたもの。

## 文脈の族

    ctxFL = [fone nil, ftwo nil]

    HCx ctxFL
    HCx ctx → JkA A → GOK (plug ctx A) → HCx (ctx ++ [fone A, ftwo nil])   -- 幅 1 のブロック
    HCx ctx → JkA A → GOK (plug ctx A) → HCx (ctx ++ [fone A])             -- 幅 0 のブロック

    HDx [fone nil]
    HCx ctx → JkA A → GOK (plug ctx A) → HDx (ctx ++ [fone A])

側条件が `GOK (plug ctx A)` だけなのが要点。族（`APd` / `WPd` / `WFd` / `WGd`）は
文脈の中の木にも族の述語を要求するので満たせなくなる。

## 壁の還元（全部緑・族を使わない）

    ZAppend D Z := ∀ M, JkA M → GOK (plug D M) → GOK (plug D (two M Z))
    SAppend D Z := ∀ M, JkA M → GOK (plug D M) → GOK (plug D (one M Z))

    ZSib := ∀ D A, HDx D → JkA A → GOK (plug D (two nil A)) → ZAppend D A
    SSib := ∀ D A' A, HCx D → JkA A' → GOK (plug D A') → JkA A →
              GOK (plug D (one A' A)) → SAppend D A

    HFone := ∀ ctx A, HCx ctx → JkA A → GOK (plug ctx A) → GOK (plug ctx (one A nil))

    ZSib ∧ SSib → HFone → QFL [] → Pay2 → hang6_R375m → R375m (6,1,0) ∈ W 0

緑の部品:

    HFone_of_Sibs / R375m61_of_Sibs
    TowHCx（幅 0 のブロックの塔は HFone 1 本で立つ）/ QH0 / QFL0_of_HFone
    PZ_cons（荷の W 帰納、2 の記録版）/ PS_cons（同、1 の記録版）
    QFL_cons（鎖の入れ子帰納法、無条件）/ QFL_all / Pay2_of_QFL0
    APnil_gen0（荷さえ吊れれば裸の 1 の記録は継げる）
    GOK_oneUV_RunSB（階段）/ GOK_appJ_tow（塔は文脈を伸ばすだけ）
    W0_acc（荷の展開 1 手は `W 0` の上で整礎）

## 残り 2 手の中身

どちらも「記録の左の兄弟を、手元にある 1 つから一般の良い木へ広げる」。

- `ZSib`: `GOK (plug D (two nil A))` から `GOK (plug D (two M A))`。
  `M` は実際には `PZ_cons` の作る鎖 `FLrZ A Bs`（＝ `TChain nil A`）に限ってよい。
- `SSib`: `GOK (plug D (one A' A))` から `GOK (plug D (one M A))`。
  `M` は `OChain A' A`（`AYsF` の鎖）に限ってよい。

既存の `TSib` / `OSib` の還元表（notes 追記参照）だと

    TSib D (one A B) ⟸ TSib D A, ∀W OSib (D ++ [ftwo W]) B
    TSib D (two A B) ⟸ TSib D A, ∀W TSib (D ++ [ftwo W]) B
    TSib D (pay A Y) ⟸ TSib D A                  （TSib_pay、緑）
    TSib D nil       ⟸ SelfW D W（自分の上に積み続けられる）

で木は縮むが文脈が伸び、`nil` のところで文脈が 1 縮んで木が任意に戻る。
`（木の大きさ, 文脈の長さ）` のどちらの辞書式順序でも割れる。ここが測度の問題。

## 死んだ道（族）

族 `WPd` / `WFd` / `WGd` は構造的に塞がっている。
**階段は塔を「予算 1 下げ・幅 1 下げ」で積み、鎖は兄弟を開いて「幅だけ 1 上げ」る。**
鎖は幅の余裕を 1 消費するのに補充できないので、兄弟条件の下限で必ず割れる。
`lo(i)` を兄弟条件の下限、`f(w)` を幅 `w` の空木に要る予算とすると
`f(i+1) ≤ lo(i)`（鎖）と `f(i+1) = lo(i)+1`（階段）で矛盾。
詳細は notes 追記282〜287。
