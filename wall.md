# 残っている壁

トリオ数列（3 行バシク行列, BM4, z < 2 の断片）の停止性証明。

2026-09-10 更新。

## 壁の連鎖（全部 Lean で緑）

    RPay    : ∀ D V, GOK (plug D V) → ∀ C, Bok C → GOK (plug D (pay V C))
                                                        （荷を 1 個吊るす）
      ↓ APnil_gen0
    RStep0  : ∀ D V, GOK (plug D V) → GOK (plug D (one V nil))
                                                        （裸の 1 の記録を 1 個積む）
      ↓ RStep_rep
    RStep (replicate q nil) nil : … → GOK (plug D (one V (stk q)))
                                                        （走りを積む）
      ↓ GOK_oneNN_of_RStep / GOK_blkNN_of_RStep
    NStep N D0（N が走り RunS (Bs ++ [B]) のとき）
      ↓ WRep_of_NStep
    WRep → WallT / TTwo / NTwUp → シート証明中の行

**つまり `N` が走りのときの壁は `RPay` 1 本**（「荷を 1 個吊るせる」）。

## 残っている穴

`N` が走りでないとき（語の最後の記録への祖先鎖に 1 の記録があるとき）。
`hMy`（`snocYd_mem` の条件）が落ちる。

ただしこれは**分割点の取り方**の問題らしい。`snocYd_mem` は語を
`Y0 ++ M ++ [(L+dl, y, 0)]` と割るので、`M` をバッドルート（鎖の最後の
1 の記録）から始めれば `M` の中の右からの最小値は全部 2 の記録になる。
木で言うと `N = plug E (one A Y)` と書いて

    plug D (one N N) = plug (D ++ [fone N] ++ E) (one A Y)

とし、`GOK_oneUV_genM` をより深い文脈で使う。次はこれを実装する。

## 部品（緑）

    RunP [A1,…,Ap] X = two A1 (… (two Ap X))    RunS As = RunP As nil
    UtwP Bs B n = 塔（1 段は「(1,0) + RunP Bs B」）
    PBlk Bs V   = fone V :: Bs.map ftwo         RBlk As = PBlk As nil
    ABt Bs B n  = appJ B (UtwP Bs B n)
    RFam Bs D0  = D0 に Bs の枠列を足してできる文脈の族、RFam_GOK はその帰納
    My_RunP / hMy_RunP
    GOK_oneNN_genM / GOK_blkNN_genM / GOK_oneUV_genM（元の 3 つの抽象版）
    NFam / NFam_GOK / WRep / GOK_twoTwoNil_rep
    NoRun / NTw_of_NoRun / STw_TTw

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
経緯は `notes.md` の追記175〜190。
