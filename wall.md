# 残っている壁（1 文）

トリオ数列（3 行バシク行列, BM4, z < 2 の断片）の停止性証明で、
シートの**証明中の行と目標の行が同じ 1 文に合流した**。その 1 文の問題文。

2026-09-10 更新。前の版（層 `TwSt` の `WallT`）は不要になった。

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

## 合流した 1 文

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

次のどちらか。

1. (b) を `GoodFb` の 3 フィールド（`pu` / `pk` / `seg`）で直接組む。
   道具は `GoodFb_snoc_dupJt0` / `GoodFb_snoc_innerJt0`（どちらも緑、文脈一般）。
   `GOK_oneUV_gen` / `GOK_blkNN_gen` が `snocYd_mem` で同じことをしているので、その写し。

2. (a) を出す理屈。兄弟が無制限の裸の 1 の記録。

## 参考

Lean のファイルは `lean/Small.lean`（約 61000 行、緑、`sorryAx` なし）。
設計の経緯は `notes.md` の追記175〜179。
