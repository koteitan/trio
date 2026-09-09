# 残っている壁（1 文）

トリオ数列（3 行バシク行列, BM4, z < 2 の断片）の停止性証明で、
シートの証明中の行 #14 が 1 つの補題に帰着している。その 1 文の問題文。

## 記法

木 `Jk1`:

    nil | one N M | two N M | pay N Y

木から行列（語）への写像 `jk1 l : Jk1 -> TrioSeq`（`l` は高さ）:

    jk1 l nil       = []
    jk1 l (one N M) = jk1 l N ++ ((l+1,1,0) :: jk1 (l+1) M)
    jk1 l (two N M) = jk1 l N ++ ((l+1,2,0) :: jk1 (l+1) M)
    jk1 l (pay N Y) = jk1 l N ++ shiftr01 (l+1) 0 Y

`two N M` は「左兄弟 N、直上の子 M を持つ 2 の記録」。

文脈は枠のリスト `List Frm`、`Frm = fone Jk1 | ftwo Jk1`。
`plug : List Frm -> Jk1 -> Jk1` は最後の枠が最も内側:

    plug (D ++ [fone U]) T = plug D (one U T)
    plug (D ++ [ftwo N]) T = plug D (two N T)

`GOK X` = 「どの良い語の右にも X の語を継いでよい」（`GoodFb` を保つ）。

## 梯子 `TwSt`

`TwSt r m D` = 文脈 D の形。`r` は 2 の枠の本数 - 1、`m` は最も内側の 2 の枠より
上の 1 の枠の本数。

    TwSt 0 m D        = StkOk (m+1) D                      （2 の枠 1 本 + 1 の枠 m+1 本）
    TwSt (r+1) 0 D    = ∃ m' D' N, D = D' ++ [ftwo N] ∧ TwSt r m' D' ∧ Fter r m'
                                   ∧ JkA N ∧ NTw r N
    TwSt (r+1) (m+1) D = ∃ D' U, D = D' ++ [fone U] ∧ TwSt (r+1) m D' ∧ JkA U
                                   ∧ (∀ D'', TwSt (r+1) m D'' -> GOK (plug D'' U))

    Fter r m = (r = 0 ∨ 0 < m)          （2 の枠の直下は必ず 1 の枠）
    TwOk r m X = ∀ D, TwSt r m D -> GOK (plug D X)
    NTw r N    = ∀ j D, TwSt r j D -> Fter r j -> GOK (plug D N)

`NTw r N` は「N はレベル r のどの文脈でも良い」。**レベル r で頭打ち**。

## 壁

    WallT : ∀ r, TwOk (r+1) 0 (two nil nil)

行列で言うと、文脈が `... [N の語] (l+1,2,0)` で終わっているとき、その直上に
もう 1 本 2 の記録 `(l+2,2,0)` を置いてよいか。つまり

    ... [N の語(高さ l)] (l+1,2,0) (l+2,2,0)

が良いか。**2 の記録が 2 の記録の直上に来る形**（走り 2）。

これが出れば
`TwOk_TWt -> TTwA_TWt -> TwoOk_TWt -> TowOk -> R14_mem`
と 4 本の補題で

    (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,2,0)(5,2,0) ∈ W 0

が出る（Lean で `TowOk_of_WallT` / `R14_of_WallT` として緑）。

## なぜ出ないか

走り 2 の階段（BM4 の展開が作る近似列）は

    two N (nstN N k),   nstN N 0 = nil,  nstN N (k+1) = one nil (two N (nstN N k))

で、語は

    [N(l)] (l+1,2,0) (l+2,1,0) [N(l+2)] (l+3,2,0) (l+4,1,0) [N(l+4)] (l+5,2,0) ...

**兄弟 N が 2 の記録を跨いで何度も複製される**。k 段目の N はレベル `r+k` の位置に
いるので、階段を通すには `∀ q, NTw q N`（全レベル）が要る。文脈が渡すのは
`NTw r N` だけ。差はこれだけ。

証明済み（緑）:

    TwOk_twoTwoNil : (∀ q, NTw q N) -> Fter r m -> TwOk r m (two N (two nil nil))
    TwOk_twoNilE   : TwOk (r+1) 0 nil            （階段が 1 の枠だけなのでレベルが増えない）
    TwOk_twoNil_f  : TwOk r (m+1) (two nil nil)  （1 の枠の直上なら無条件）
    TwOk_twoNilTwoNil : Fter r m -> TwOk r m (two nil (two nil nil))   （兄弟 nil なら緑）

## レベル 0 では解決している

2 の枠が 1 本だけの層（`APd` / `TwoOk`）では走りも荷も無条件に緑。

    TwoOk Z = ∀ N, JkA N -> (∀ j kk, APd (replicate j true ++ (true::kk)) N)
                 -> ∀ j kk, APd (replicate j true ++ (true::kk)) (two N Z)

兄弟条件が `∀ j kk` で **kk は任意の形**（2 の枠を何本含んでもよい）＝ 全レベル。
これが書けるのは `APd` が `TwoOk` より**先に定義済み**だから（非可述にならない）。

    APd_twoTwoGen : (N が全 shape) -> APd (true::ks) (two N (two nil nil))   -- 走り、緑
    APd_chainT'   : (N が全 shape) -> TwoOk T -> twoIt N T n も全 shape      -- 荷の横鎖、緑

`TwoOk T` は「T はどんな全 shape の兄弟の上にも乗る」なので、横鎖自身を兄弟にして
適用すると次の横鎖の全 shape 性が出る。A2'（荷の順序数についての帰納）と噛み合っている。

## 深い層で同じことをすると三すくみになる

    (a) 兄弟条件を層 X についてのものにする
        -> 枠木条件も層 X ベースでないと適用できない
    (b) 枠木条件を層 X ベースにする
        -> 層 X ⊄ 層 X' なので、先に定義済みの notion による兄弟条件が適用できない
    (c) 枠木条件を層 X'（先に定義済み）ベースにする
        -> 枠木 two nil nil が TwOk (r+1) 0 (two nil nil) = 元の壁 を要求する

試した設計 8 通り（兄弟を nil に固定 / 構文的な族 / 族 + 頭打ち / 族の tip を nil に /
層を 2 段 3 段 / 文脈をデータに / 全レベル条件を先に定義済みの APd で書く /
全レベル条件を先に定義済みの NTw で書く）。全部 (a)(b)(c) のどれかで止まる。

## 欲しいもの

次のどちらか。

1. `NTw r N` から `NTw (r+1) N` を出す理屈。
   BM4 の展開規則の側から「兄弟 N の良さがレベルを跨ぐ」理由が付けば、
   それを層の条件に書ける。

2. 走り 2 の階段を `nstN N k`（兄弟が深くに複製される）以外の形で取る方法。
   階段は `GoodFb_of_keyJ` の `hnew` に渡すもので、BM4 の展開が決めている。
   別の近似列で同じ極限に届くなら、兄弟の複製を避けられる可能性がある。

## 参考

Lean のファイルは `lean/Small.lean`（約 60000 行、緑、`sorryAx` なし）。
設計の試行錯誤は `notes.md` の追記149〜157 に全部書いてある。
