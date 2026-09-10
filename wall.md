# 残っている壁（1 文）

トリオ数列（3 行バシク行列, BM4, z < 2 の断片）の停止性証明。

2026-09-10 更新。`OneNil` が最終形。

## 結論の 1 文

    OneNil : ∀ (D : List Frm) (W : Jk1), JkA W →
        (∀ X, JkA X → JkT (plug D (one W X))) →
        GOK (plug D W) → GOK (plug D (one W nil))

**「置ける `W` の上に裸の 1 の記録を 1 個積める」— これだけ。**

**シートの 2 行が両方これ 1 本から出る**（Lean で緑）:

    R14_of_OneNil  : OneNil → (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,2,0)(5,2,0)
    R376_of_OneNil : OneNil → (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,3,0)
    OneNil_of_RPay : RPay   → OneNil

## #14 の道

    OneNil
      ↓ OneTwo_of_OneNil
    OneTwo : GOK (plug D W) → GOK (plug D (one W (two nil nil)))
      ↓ TWStep_of_OneTwo
    TWStep : GOK (plug D (two nil nil)) → GOK (plug D (TW 1))
      ↓ TowOk_of_TWStep
    TowOk → R14_mem

各段は `GOK_oneUV_RunSB`（走り、兄弟任意）＋ `GOK_appJ_UtwP`（塔を 1 ブロックに割る）。
基底 `plug TWD0 (two nil nil) = one nil (stk 2)` は `GOK_oneStk2`（既存、無条件）。

    TW 0 = two nil nil,  TW (n+1) = one (two nil nil) (two nil (TW n))
    TWBlk = [fone (two nil nil), ftwo nil],  TWD0 = [fone nil, ftwo nil]
    plug (D ++ TWBlk) X = plug D (one (two nil nil) (two nil X))
    plug D (TW (n+1))   = plug (D ++ TWBlk) (TW n)

## 行376 の道

    OneNil → RStepN0 → RStepN_rep → GOK_Utw_of_RStepN0 → UtwAll → R376_of_UtwAll

    Utw p n = UtwR (replicate p nil) n
    RBlk As = fone nil :: As.map ftwo
    plug (D ++ RBlk As) X = plug D (one nil (RunP As X))

## `OneNil` の中身

`APnil_gen0`（緑、文脈一般）で

    OneNil ⟸ ∀ C, Bok C → GOK (plug D (pay W C))     ＝ RPay（荷 1 個）

文脈の末尾で場合分けすると

    D = []      : AY0（緑、無条件）
    末尾 fone U : AYs / AYsF（緑）
    末尾 ftwo N : TSib_pay / TSibF_pay（緑、梯子なし）

兄弟の族に制限した版も両側とも緑（`OChain` / `TChain`）。
残るのは測度（下記）。

## `OneNil` は `GCtx` 文脈では緑

    OneNil_GCtx : GCtx ks ctx → FrmJ ks V → Rq ks V → APd ks V →
        GOK (plug ctx (one V nil))
    OneNil_GCtx_nil : GCtx ks ctx → GOK (plug ctx (one nil nil))

`APd_oneNil` と `APd_payA` はどちらも一般の `ks`（`false` を含む）で緑。
`APd_iff` で文脈に移すだけ。

**つまり `OneNil` の穴は「`GCtx` でない文脈」だけ。** `GCtx` からはみ出すのは

    (1) 1 の枠の木が `Rq (false::ks) U = TopOk U` を満たさない
        ＝ 2 の枠の直上に `two nil nil` を置く（`TW` の塔）
    (2) 2 の枠が連続する（走り）

の 2 つ。どちらも既知の壁。`OneNil` は新しい難しさではなく、
既知の壁ちょうどぶんだけ足りない。

## `Rq`（2 の記録の直上は `TopOk`）は主要補題から全部外れた

    AYdT'       : TopOk Z を外した（素通しで一度も使われていなかった）
    APd_payA'   : Rq なし
    AYs2        : CtxX なし（＝ Rq なし）
    APd_oneNil' : Rq なし
    MPd_oneNil  : MPd 層の one V nil

鍵は `CtxX ctx X` が `JkT_plug` のためだけに使われていたこと。

    JkA_plug' : CtxJ ctx → JkA T → JkA (plug ctx T)
    JkT_plug' : CtxOk ctx → JkA T → (ctx = [] → TopOk T) → JkT (plug ctx T)

`CtxOk ctx` があれば `ctx ≠ []` のとき先頭が 1 の枠なので `TopOk` は文脈が持つ。
`ctx = []` のときだけ `TopOk T` が要るが、`GCtx ks []` なら `ks = []` で
`FrmJ [] V = JkT V` が `TopOk` を持っている（`GCtx_cons_ne`）。

**残る `Rq` は `APd` / `GCtx` の定義に入っている分だけ。** 定義から外すと
`APd_all`（任意の `JkJ` 木を任意の形に差す）が壊れる。`MPd` はそこを
`FrQ` 枠で回避しているが、`MCtx` は 1 の枠の木に `MPd ks U` も課すので
`U = two nil nil` を `false` 頭に置くのは結局 `MNil`（`MPd` の壁）と同じ。

## 別ライン `MPd` の現状

    R14_mem_M  (MNil)   / R14_mem_A (∀ N, FrQ N → MBplus N)
    R14_mem_L  (LStep)  / R14_mem_L1 (LStep1) / R14_mem_L2 (LStep2)

    LStep2 : JkA N → AllA N → LAll N → JkA Z → LAll1 Z → LAll1 (two N Z)
      Z = nil     : LOk_twoNilA（緑）
      Z = pay A Y : LAll1_twoPay（緑、TSibF が仮定）
      Z = one/two : 走り

## 残っている測度の問題

    木の構造で降りる: 木が縮む、文脈が 1 伸びる
    荷（APnil_gen0）: 文脈が 1 縮む、木は任意（兄弟 `W`）

再帰は `(k, V) → (k + jsz V, nil) → (k + jsz V - 1, 任意の W)` となり、
レベルが `jsz V` 上がってから 1 だけ下がる。`W` が無制限なので止まらない。
梯子 `TwSt` は「その形の**全文脈**で良い」を持つので木を積み上げるだけで済み、
この再帰が起きない。**明示文脈の道は梯子を再現する。**

梯子の唯一の穴は `Fter`（2 の枠の直上に 2 の枠を積めない）＝ `WallT`。
ただし荷の障害は消えた（`TSib_pay` は `Fter` を要求しない）。残るのは
`GOK_twoNil_gen` / `GOK_twoTwoNil_gen` が「1 の枠止まりの文脈」を要求すること。

## 壁の正体は「レベル ⇄ 走りの長さ」の交換

    plug (D ++ [ftwo N]) (RunS Bs) = plug D (RunS (N :: Bs))

レベルが 1 下がるかわりに走りが 1 本伸びる。追記171 の「非可述性の正体は
2 の枠の本数」と、走りの長さの帰納（`WRunB`）は同じものの 2 つの見方だった。

## 部品（緑）

    AY0 / AYs / AYsF / OChain / GOK_chainJF / APnil_gen0
    TSib_pay / TSibF_pay / TChain / GOK_twoIt_chainF / GOK_twoIt_chain
    OSib / TSib / TSibF / SelfW / TSib_nil_of_SelfW / TSibF_nil_of_SelfW
    OneNil / OneTwo / TWStep / TWBlk / TWD0 / TowOk_of_TWstep / GOK_oneStk2
    RStepN / RStepN_rep / RStep / RStep_of_RPay / RStep_snoc / RStep_rep
    RunP / RunS / UtwP / UtwR / PBlk / RBlk / ABt / RFam / RFam_GOK
    GOK_appJ_UtwP / GOK_two_UtwP / GOK_ABt_of_step / NFam / NFam_GOK
    JkT_RFam_PBlk / JkT_RFam_RBlk / JkT_RFam_TWBlk
    My_RunP / hMy_RunP / jk1_RunS_snocB / jsz / jsz_RunP
    GOK_oneNN_genM / GOK_blkNN_genM / GOK_oneUV_genM / GOK_oneUV_RunSB
    TwSt_split3 / GOK_oneN_split / GOK_blkN_split / plug_blk2
    WRep / GOK_twoTwoNil_rep / NoRun / NTw_of_NoRun / STw_TTw / WallT_of_TSib

## 木の帰納の表（レベル添字版、参考）

    STw X = ∀ q, NTw q X          TTw X = ∀ q, TwOk (q+1) 0 X

    X          STw                        TTw
    -------------------------------------------------------------
    nil        NTw_nil                    TwOk_twoNilE
    one A B    STw A, STw B → 緑          TTw A, STw B → 緑
    pay A Y    STw A → 緑                 TTw A → 緑
    two A B    STw A, TTw B → 緑          ★ 壁 = TTwo
    -------------------------------------------------------------

`TTwo := ∀ A B, JkA A → JkA B → STw A → TTw B → TTw (two A B)`。
最小の場合 `A = B = nil` が `WallT`。`NTwUp` は `TTwo` から出る。
これまで出てきた壁

    WallT / WallP / Wall / OneGap / TwoStep / BStairAll / QPayPair
    WStep0 / WPay / LTwo (two nil nil) / NTwUp / TTwo / WRep

は全部 `NStep` に合流する。

## なぜレベル添字が邪魔だったか

`TwSt (r+1) 0` の文脈は `D' ++ [ftwo N]` の形で、持っている条件は

    NTw r N        ← レベル r で打ち止め

一方 `TwOk_twoTwoNil` は `∀ q, NTw q N`（全レベル）を要求する。
`NStep` は文脈を**具体的に**取るので、この差が消える。

## レベル 0 では壁は無い

    AUni N  = ∀ j kk, APd (rep j true ++ (true::kk)) N     （全 shape で良い）
    TwoOk Z = ∀ N, JkA N → AUni N → AUni (two N Z)

- `TwoOk_twoNil : TwoOk (two nil nil)` は緑。
- `LOk_twoNilAll : ∀ k, LOk k (two nil nil)` は緑（`LOk 0 ⟺ TwoOk`）。

つまり `StkOk`（梯子のレベル 0）では「2 の記録の直上の 2 の記録」は解けている。
理由は `StkOk 0` の 2 の枠の木 `N` が `AUni N`（全 shape 一様）を持っているから。
`APd_chainT'` の通り `AUni` は `twoIt N T n` で閉じている。

一方 `TwSt (r+1) 0` の 2 の枠の木 `N` は `NTw r N`（レベル r で打ち止め）しか持たない。

**壁 = 梯子の 2 の枠の木が一様でないこと。** 差はそこだけ。

## 梯子を作り直す道が塞がっている理由

2 の枠の欄を強めた梯子 `TwSt'` を作ると、必ず次のどちらかで詰まる。

1. 1 の枠の欄を **素の `TwSt` 相対**にすると `TwSt' ⊆ TwSt` が出るので
   `TwOk_twoTwoNil` がそのまま使えて `WallT'` は緑。しかし `TwOk_TWt`
   （`TW (n+1) = one (two nil nil) (two nil (TW n))`）が 1 の枠に
   `two nil nil` を積むので、素の `TwOk (r+1) 0 (two nil nil)` = `WallT` が要る。
2. 1 の枠の欄を **`TwSt'` 相対**にすると `TwOk_TWt` は `WallT'` から回る。
   しかし `TwSt' ⊆ TwSt` が消えるので `TwOk_twoTwoNil` を移植する必要があり、
   その連鎖が `TwOk'_nil → TwOk'_pay → TwOk'_pay_e → TwOk'_twoIt` まで届く。
   `TwOk'_twoIt` は `ftwo (twoIt N T n)` を積むので、2 の枠の欄の条件が
   `twoIt N T n` で閉じていなければならない。`NoRun` は閉じていない。
   全レベル一様 `∀ q, NTw' q N` にすると定義が循環する。

`AUni N` を欄に入れる案も、`r = 0` で `AUni X → LOk (j+1) X` が必要になって止まる。
`LOk` の 1 の枠は意味的（弱い）ので `APd` からは出ない。

## 壁が無い木の族（緑）

    NoRun nil
    NoRun A → NoRun B → NoRun (one A B)
    NoRun A → NoRun B → TopOk B → NoRun (two A B)
    NoRun A → Bok Y → NoRun (pay A Y)
    NoRun A → NoRun (two A (two nil nil))

    NTw_of_NoRun : NoRun X → ∀ q, NTw q X      -- 緑

上の表の緑のマスだけで閉じる族。壁は「走りを含む兄弟」だけに残っている。

## 記法

木 `Jk1`:

    nil | one N M | two N M | pay N Y

木から行列（語）への写像 `jk1 l : Jk1 -> TrioSeq`（`l` は高さ）:

    jk1 l nil       = []
    jk1 l (one N M) = jk1 l N ++ ((l+1,1,0) :: jk1 (l+1) M)
    jk1 l (two N M) = jk1 l N ++ ((l+1,2,0) :: jk1 (l+1) M)
    jk1 l (pay N Y) = jk1 l N ++ shiftr01 (l+1) 0 Y

`one N M` / `two N M` は「左兄弟 N、直上の子 M を持つ 1 / 2 の記録」。
`pay N Y` は N の上に荷 Y（`Bok Y`、それ自体が良い行列）を吊るす。

文脈は枠のリスト `List Frm`、`Frm = fone Jk1 | ftwo Jk1`。

    plug [] T                 = T
    plug (fone N :: rest) T   = one N (plug rest T)
    plug (ftwo N :: rest) T   = two N (plug rest T)

`GOK X` = 「どの良い語の右にも X の語を継いでよい」（`GoodFb` を保つ）。

## 層を通らない言い換え `WStep0`（参考）

    WCtxT ctx V := ∀ X : Jk1, JkA X → JkT (plug ctx (one V X))     -- 字レベルの妥当性だけ
    WV V        := V = nil ∨ V = two nil nil
    Wblk V p    := fone V :: (ftwo nil)^p
    WFam        := [] から Wblk V p（WV V）を積んで作る文脈の族

    WStep0 := ∀ ctx, WFam ctx → ∀ V, WV V → WCtxT ctx V → GOK (plug ctx V)
                → GOK (plug ctx (one V nil))

**「裸の 1 の記録をどの文脈でも置ける」— これだけ。**

これが出れば

    R14_of_WStep0  : WStep0 → (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,2,0)(5,2,0)
    R376_of_WStep0 : WStep0 → (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,3,0)

がどちらも出る（Lean で緑）。**層（`APd` / `Cok` / `Pok` / `TwSt`）を一切通らない。**

## どうやってここまで落ちたか

要は「主張を文脈について全称にすると、階段が文脈を伸ばしても帰納が回る」。

    plug ctx (one V (stk (p+1)))          stk q = 走り q（(l+1,2,0)…(l+q,2,0)）
      の階段は appJ V (Utw p k) で、これは plug (ctx ++ Wblk V p) (Utw p k) に等しい

    Utw p k = ブロック「(1,0) + 走り p」を k 個積んだ木

`k` について内側の帰納（文脈が伸びても主張は全称なので当たる）、
`p` について外側の帰納（走りが 1 段短くなる）。これで走りが層なしで通る（`WRun`）。

塔（証明中の行の展開列）も同じ形になる。

    TW 0 = two nil nil,  TW (n+1) = one (two nil nil) (two nil (TW n))
    plug ctx (one V (two nil (TW (n+1)))) = plug (ctx ++ Wblk V 1) (one (two nil nil) (two nil (TW n)))

底は `two nil (TW 0) = stk 2` なので `WRun` の走り 2。

## `WStep0` の中身

`APnil_gen0`（緑、文脈一般）が

    APnil_gen0 ctx V (JkT (plug ctx (one V nil))) (GOK (plug ctx V))
      (hang : ∀ C, Bok C → GOK (plug ctx (pay V C)))
      : GOK (plug ctx (one V nil))

なので、残るのは **`hang`（荷 1 個）**だけ。

    ctx = []  → AY0（緑、無条件）。荷の複製が「項ごとの繰り返し」で済む
    ctx ≠ []  → 下記の 2 つの形が残る

## 残っている 2 つの形

    (a) 兄弟が無制限の裸の 1 の記録
          ∀ W, CtxX ctx W → GOK (plug ctx W) → GOK (plug ctx (one W nil))

    (b) 走りの上の荷
          GOK (plug ctx (pay (two nil nil) C))      ctx の末尾が ftwo nil

(a) は `AYs`（緑、文脈一般の荷の補題）の仮定 `hAP` がそのまま要求するもの。

    AYs Y (Bok Y) ctx (CtxOk ctx) X Z (CtxX ctx X) (CtxT ctx Z)
        (hAP : ∀ V, CtxX ctx V → GOK (plug ctx V) → GOK (plug ctx (one V Z)))
        (GOK (plug ctx X))
      : GOK (plug ctx (one X (pay Z Y)))

`AYs` の証明を読むと `hAP` が当たるのは `X` と鎖 `itJ (pay Z Y') k X` だけなので、
`hAP` を族に制限した版は原理的に作れる。ただしその鎖が `{nil, two nil nil}` から出る。

(b) は既存の機械が**全部弾く**形。`AYs` は `CtxX`、`APd` は `Rq` で

    CtxXJ [ftwo _] X = JkA X ∧ TopOk X
    Rq (false :: ks) U = TopOk U

を要求し、`TopOk (two nil nil) = False` だから。行列で見ると

    …(d,2,0)(d+1,2,0)     ← 走り

になるので、走りを表現できない記法では書けない。

実測（`bms`）では (b) の展開は

    …(3,1,0)(4,2,0)(5,2,0)(6,0,0)  →  …(3,1,0)(4,2,0)(5,2,0)(5,2,0)

で、**証明中の行の行列そのもの**。横鎖 `twoIt nil (pay X C') k`（同じ高さに 2 の記録が
横に並ぶ、delta = 0）が出る。

## 欲しいもの

次のどれか。

1. `GOK_oneNN_gen` / `GOK_blkNN_gen` の `hNs`（N が走り）を外した一般版。
   一般の N では `one N N` の語の最後の記録が N の形で変わるので、
   バッドルートの場合分けが増える。そこを `GoodFb` の 3 フィールド
   （`pu` / `pk` / `seg`）だけで書けるか。

2. `NStep` の階段を実測して、一般の N でも `Utw p n` 型の塔になるか確かめる。
   なるなら `GOK_oneNN_gen` の証明がほぼそのまま通る。

3. `NStep` の第 2 文だけを先に落とす。第 1 文（`one N N`）は
   `NTw r N` の文脈では `TwOk_itJ` で無料なので、
   `[ftwo N, fone nil]` を足す第 2 文が本体。

## 木の側の走りは解けている（参考）

走り（`stk q` = `(l+1,2,0)…(l+q,2,0)`）を**木の先端**に置く問題は、
主張を文脈について全称にすると解ける。

    WRun : ∀ p ctx V, … → GOK (plug ctx V) → GOK (plug ctx (one V (stk p)))

`GOK_oneUV_gen` の階段 `appJ V (Utw p k)` が `plug (ctx ++ Wblk V p) (Utw p k)` と
等しいので、`k` について内側の帰納（文脈が伸びても主張は全称なので当たる）と
`p` について外側の帰納（走りが 1 段短くなる）で回る。

    Wblk V p = fone V :: (ftwo nil)^p
    Utw p k  = ブロック「(1,0) + 走り p」を k 個積んだ木

**文脈**の側の走り（＝左兄弟のレベル一様性）はこれでは解けない。それが `TTwo`。

## 参考

Lean のファイルは `lean/Small.lean`（約 61000 行、緑、`sorryAx` なし）。
経緯は `notes.md` の追記175〜206。
