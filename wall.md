# 壁

シート行376 `(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,3,0)`。

## いま開いている最小の行列（bms で実測）

    R375m (6,1,0) = (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,2,0)(6,1,0)
    標準形。展開は TwD 6 R375m (n+1)（R375m 自身の縦塔）。

木では `bdA [2,0]`（幅 2 のブロックの上に裸の 1 の枠）を台座 `R341` の上に置いたもの。

## 壁は 1 文

    OSib D X := ∀ M, JkA M → GOK (plug D M) → GOK (plug D (one M X))
    TSib D X := ∀ M, JkA M → GOK (plug D M) → GOK (plug D (two M X))

    HGx [fone nil]
    HGx ctx → JkA A → GOK (plug ctx A) → HGx (ctx ++ [fone A])
    HGx ctx → JkA A → GOK (plug ctx A) → HGx (ctx ++ [ftwo A])

    GNilO := ∀ D, HGx D → OSib D nil      ★これ 1 本
    GNilT := ∀ D, HGx D → TSib D nil

    GNilO → HFone → QFL [] → Pay2 → hang6_R375m → R375m (6,1,0) ∈ W 0

族の述語（`APd` / `WPd` / `WFd` / `WGd`）を文脈の中の木に要求していたのが
充足可能性の壁だった。`HGx` の側条件は `GOK` だけなので、それは消えた。

## 還元の地図（`GNilO` / `GNilT` を仮定に置いたとき）

| 場合 | 道具 | 状態 |
|---|---|---|
| `GNilO`（`D` が 1 の枠止まり） | `APnil_gen0` + `PS_cons` + `GSib_tree` | 緑 `GNilO_fone` |
| `GNilO`（`D` が 2 の枠止まり） | `APnil_gen0` + `PZ_cons` + `GSib_tree` | 緑 `GNilO_ftwo` |
| `GNilO`（`D = [fone nil]`） | `GOK_oneOneNil` | `APz M` に落ちる `GNilO_base` |
| `GNilT`（`D` が 1 の枠止まり） | `TSib_nil_of_SelfW` + `SelfW_HGx` | 緑 `GNilT_fone` |
| `GNilT`（`D` が 2 の枠止まり） | `GAll_of_GNils` | 緑（走りも含めて出る） |

## 還元はもう終わっている

    GAll := ∀ F, HGx F → ∀ Z, JkA Z → GOK (plug F Z)

    GAll_of_GNils : GNilO → GNilT → (∀ Z, JkA Z → GOK (one nil Z)) → GAll
    GNilO_of_GAll / GNilT_of_GAll / GAllBase_of_GAll

つまり

    GAll ⟺ GNilO ∧ GNilT ∧ (∀ Z, JkA Z → GOK (one nil Z))

で、`GAll` はこの符号化での z < 2 の停止性そのもの。どの場合も他の場合へ
還元できるので、**これ以上還元することは無い**。残っているのは整礎な測度だけ。

## 緑の部品

    HFone_of_GNilO / R375m61_of_GNilO
    GSib_tree（木の構造帰納）/ SelfW_HGx（自分の上に積み続ける）
    hangG_fone / hangG_ftwo（荷の還元）
    OSib_one / OSib_two / TSib_one / TSib_two（plug の付け替えだけ）
    PS_cons / PZ_cons（荷の W 帰納、CtxJT だけで回る）
    PS_consF / TSibF_pay（兄弟を鎖 OChain / TChain に制限した版）
    HCx / HDx / TowHCx / QH0 / QFL0_of_HFone（幅 0 のブロックの塔）
    QFL_cons（鎖の入れ子帰納法、無条件）/ QFL_all / Pay2_of_QFL0
    GOK_oneUV_RunSB（階段）/ GOK_appJ_tow（塔は文脈を伸ばすだけ）
    W0_acc（荷の展開 1 手は `W 0` の上で整礎）

## 測度（未解決）

`GNilO (D ++ [fone V])` ⟸ `GNilO / GNilT (D ++ M の背骨の枠)`。
長さは `|D| + 1` → `|D| + h(M)`（`h(M)` は `M` の背骨の記録の本数）。
`h(M) ≤ 0`（`M` が `nil` か荷だけ）でないと減らない。`M` は兄弟なので任意。
`（木の大きさ, 文脈の長さ）`のどちらの辞書式順序でも割れる。

## 死んだ道（族）

族 `WPd` / `WFd` / `WGd` は構造的に塞がっている。
**階段は塔を「予算 1 下げ・幅 1 下げ」で積み、鎖は兄弟を開いて「幅だけ 1 上げ」る。**
鎖は幅の余裕を 1 消費するのに補充できないので、兄弟条件の下限で必ず割れる。
`lo(i)` を兄弟条件の下限、`f(w)` を幅 `w` の空木に要る予算とすると
`f(i+1) ≤ lo(i)`（鎖）と `f(i+1) = lo(i)+1`（階段）で矛盾。
詳細は notes 追記282〜287。
