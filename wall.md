# 壁

シート行376 `(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,3,0)`。

## いま開いている最小の行列（bms で実測）

    R375m (6,1,0) = (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,2,0)(6,1,0)
    標準形。展開は TwD 6 R375m (n+1)（R375m 自身の縦塔）。

木では `bdA [2,0]`（幅 2 のブロックの上に裸の 1 の枠）を台座 `R341` の上に置いたもの。

## 壁は 1 文

    OSib D X := ∀ M, JkA M → GOK (plug D M) → GOK (plug D (one M X))
    TSib D X := ∀ M, JkA M → GOK (plug D M) → GOK (plug D (two M X))

    HEx [fone nil]
    HEx ctx → JkA A → HEx (ctx ++ [fone A])
    HEx ctx → JkA A → HEx (ctx ++ [ftwo A])

    NilO := ∀ D, HEx D → OSib D nil      ★これ 1 本
    NilT := ∀ D, HEx D → TSib D nil

    NilO → HFone → QFL [] → Pay2 → hang6_R375m → R375m (6,1,0) ∈ W 0

`HEx` には**側条件が 1 つもない**（枠の木は `JkA` なだけ）。族
（`APd` / `WPd` / `WFd` / `WGd`）が文脈の中の木にも族の述語を要求して
満たせなくなっていたのが、これで消えた。

## 緑の部品

    HFone_of_NilO / R375m61_of_NilO
    Sib_tree : NilO → NilT → ∀ T, JkA T → ∀ D, HEx D → OSib D T ∧ TSib D T
    NilO_of_hang（APnil_gen0 の包み直し）
    OSib_one / OSib_two / TSib_one / TSib_two（plug の付け替えだけ）
    PS_cons / PZ_cons（荷の W 帰納、CtxJT だけで回る）
    PS_consF / TSibF_pay（兄弟を鎖 OChain / TChain に制限した版）
    HCx / HDx（GOK 側条件つきの塔の文脈）/ TowHCx / QH0 / QFL0_of_HFone
    QFL_cons（鎖の入れ子帰納法、無条件）/ QFL_all / Pay2_of_QFL0
    GOK_oneUV_RunSB（階段）/ GOK_appJ_tow（塔は文脈を伸ばすだけ）
    W0_acc（荷の展開 1 手は `W 0` の上で整礎）

## `NilO` の中身と、残る測度の問題

`NilO D` は `APnil_gen0` で荷に落ちる:

    NilO D ⟸ ∀ M 良い, ∀ C Bok, GOK (plug D (pay M C))

`D` の最後の枠で分けると

    D = D' ++ [fone V] : plug D' (one V (pay M C)) → PS_cons → OSib D' M
    D = D' ++ [ftwo V] : plug D' (two V (pay M C)) → PZ_cons → TSib D' M
    D = [fone nil]     : one nil (pay M C) → AYs（深さ 0）→ APz M

そして `OSib D' M` / `TSib D' M` は `Sib_tree` で `M` の構造帰納:

    OSib D (pay Z Y) ⟸ OSib D Z                        （PS_cons）
    OSib D (one N T) ⟸ OSib D N, ∀W OSib (D ++ [fone W]) T
    OSib D (two N T) ⟸ OSib D N, ∀W TSib (D ++ [fone W]) T
    TSib D (one N T) ⟸ TSib D N, ∀W OSib (D ++ [ftwo W]) T
    TSib D (two N T) ⟸ TSib D N, ∀W TSib (D ++ [ftwo W]) T
    OSib D nil / TSib D nil = 壁

**木は縮むが文脈が伸びる。`nil` のところで文脈が 1 縮んで木が任意に戻る。**
`（木の大きさ, 文脈の長さ）` のどちらの辞書式順序でも割れる。これが最後の
測度の問題で、`TSib D nil` は `SelfW D M`（`M` を自分の上に積み続けられる）
＝ `GOK_twoNil_gen` の階段に対応する。

## 死んだ道（族）

族 `WPd` / `WFd` / `WGd` は構造的に塞がっている。
**階段は塔を「予算 1 下げ・幅 1 下げ」で積み、鎖は兄弟を開いて「幅だけ 1 上げ」る。**
鎖は幅の余裕を 1 消費するのに補充できないので、兄弟条件の下限で必ず割れる。
`lo(i)` を兄弟条件の下限、`f(w)` を幅 `w` の空木に要る予算とすると
`f(i+1) ≤ lo(i)`（鎖）と `f(i+1) = lo(i)+1`（階段）で矛盾。
詳細は notes 追記282〜287。
