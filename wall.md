# 残っている壁（1 文）

トリオ数列（3 行バシク行列, BM4, z < 2 の断片）の停止性証明で、
シートの証明中の行 #14 が 1 つの補題に帰着している。その 1 文の問題文。

**2026-09-10 更新。壁（走り 2）は解けた。残っているのは荷（`pay`）だけになった。**

## 記法

木 `Jk1`:

    nil | one N M | two N M | pay N Y

木から行列（語）への写像 `jk1 l : Jk1 -> TrioSeq`（`l` は高さ）:

    jk1 l nil       = []
    jk1 l (one N M) = jk1 l N ++ ((l+1,1,0) :: jk1 (l+1) M)
    jk1 l (two N M) = jk1 l N ++ ((l+1,2,0) :: jk1 (l+1) M)
    jk1 l (pay N Y) = jk1 l N ++ shiftr01 (l+1) 0 Y

`two N M` は「左兄弟 N、直上の子 M を持つ 2 の記録」。`pay N Y` は N の上に荷 Y を吊るす。

文脈は枠のリスト `List Frm`、`Frm = fone Jk1 | ftwo Jk1`。
`plug : List Frm -> Jk1 -> Jk1` は最後の枠が最も内側:

    plug (D ++ [fone U]) T = plug D (one U T)
    plug (D ++ [ftwo N]) T = plug D (two N T)

## 目標

    #14 = (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,2,0)(5,2,0)

`bms` で実測すると

    good part = (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)
    bad part  = (3,1,0)(4,2,0)(5,2,0)      delta = 2

    [1] … (3,1,0)(4,2,0)(5,2,0) (5,1,0)(6,2,0)(7,2,0)
    [2] … (3,1,0)(4,2,0)(5,2,0) (5,1,0)(6,2,0)(7,2,0) (7,1,0)(8,2,0)(9,2,0)

これは木で `one nil (two nil (TW n))` の語。

    TW 0     = two nil nil
    TW (n+1) = one (two nil nil) (two nil (TW n))

    TowOk := ∀ n, GOK (one nil (two nil (TW n)))

`TowOk` から #14 が出る（Lean で `R14_mem` として緑）。n = 0,1,2 は個別に緑。

## 層 `Qok` / `Qk`

添字は (対の段数 j, 1 の枠の本数 n)。台は `TipOk`（＝「左兄弟が一様な 2 の記録の直上に
置ける」）。**2 の枠の左兄弟を `nil` に固定**してある。

    Qok 0 0 ctx       = (ctx = [])
    Qok 0 (n+1) ctx   = ∃ U ctx', ctx = ctx' ++ [fone U] ∧ Qok 0 n ctx' ∧ JkA U ∧
                          (∀ cs, Qok 0 n cs → TipOk (plug cs U)) ∧ (荷つき版)
    Qok (j+1) 0 ctx   = ∃ V Wl ctx' n, ctx = (ctx' ++ [fone V]) ++ [ftwo Wl] ∧
                          Qok j n ctx' ∧ JkA V ∧ (∀ cs, Qok j n cs → TipOk (plug cs V)) ∧
                          (荷つき版) ∧ JkA Wl ∧
                          (∀ i cs, Qok j (i+1) cs → TipOk (plug cs Wl)) ∧ (荷つき版) ∧
                          **Wl = nil**
    Qok (j+1) (n+1) ctx = （1 の枠を足すだけ、`Qok 0 (n+1)` と同型）

    Qk j n Z := ∀ ctx, Qok j n ctx → TipOk (plug ctx Z)

## 解けた部分（緑）

    Qk_nil        : ∀ j n, Qk j n nil
    Qk_one        : Qk j n U → (荷) → Qk j (n+1) T → Qk j n (one U T)
    Qk_pair       : Qk j n V → (荷) → (∀ i, Qk j (i+1) Wl) → (荷) → Wl = nil →
                    Qk (j+1) 0 T → Qk j n (one V (two Wl T))
    Qk_twoW       : Qk (j+1) 0 T → Qk j (n+1) (two nil T)
    Qk_nstT       : ∀ k j, Qk (j+1) 0 (nstN2 nil nil k)          -- 交互塔
    Qk_twoNilNil  : ∀ j, Qk (j+1) 0 (two nil nil)                -- ★ 走り 2 の壁
    Qk_TW         : ∀ n j, Qk (j+1) 0 (TW n)
    TowOk_all / R14_mem_final                                     -- #14

ただし `Qk_pay` 以下は仮定 `QPayPair` つき。

## 残っている 1 文

    QPayPair : ∀ (j : ℕ) (Y : TrioSeq), Bok Y → ∀ X : Jk1, JkA X →
                 Qk (j+1) 0 X → Qk (j+1) 0 (pay X Y)

「2 の枠（左兄弟 nil）の直上にある木 X に荷 Y を吊るせる」。

`n ≥ 1`（1 の枠の直上）と `(j,n) = (0,0)` は緑。`(j+1, 0)` だけが残っている。

## なぜ出ないか

荷の議論は `Y` についての A2'（`W 0` の整礎性）帰納。`Y = Y' ++ [(0,0,0)]` の場合、
`GoodFb_snoc_dupJt0` が作る近似列は

    twoIt nil (pay X Y') k = two (two (… two nil (pay X Y') …) (pay X Y')) (pay X Y')

で、**2 の記録が同じ高さに横に並ぶ**。これが次の文脈の 2 の枠の左兄弟に来る。
つまり左兄弟が `nil` でなくなる。`Qok` は `Wl = nil` を要求しているので通らない。

左兄弟の欄を緩めればよいように見えるが、そこには次の 2 つを**同時に**書く必要がある。

  (i) **横鎖について閉じている**（荷に要る）
      左兄弟が `twoIt nil T k` の形になってよいこと。
      条件はそのレベル `j` で置けるだけでよい（近似列の帰納は同じ j しか使わない）。

  (ii) **全レベルで置ける**（壁に要る）
      `Qk_twoNilNil` の階段は `two Wl (nstN2 Wl nil k)`。実測すると

          深さ1: …(3,1,0)(4,2,0)(5,2,0)          bad part = (3,1,0)(4,2,0)   delta 2
          深さ2: …(3,1,0)(4,2,0)(5,1,0)(6,2,0)(7,2,0)
                                                  bad part = (5,1,0)(6,2,0)   delta 2
          深さ3: …(3,1,0)(4,2,0)(5,1,0)(6,2,0)(7,1,0)(8,2,0)(9,2,0)
                                                  bad part = (7,1,0)(8,2,0)   delta 2

      bad root はいつも「いちばん内側の 1 の枠の列」で、bad part は
      `[fone V, ftwo Wl]` の対そのもの。だから階段は左兄弟 `Wl` を
      深さ j, j+1, …, j+k に複製する。`∀ j i, Qk j (i+1) Wl` が要る。
      （左兄弟が nil でないと bad part に兄弟の語が丸ごと入ることも実測済み。
        これは BM4 の展開規則が決めている事実で、層の設計の都合ではない。）

`nil` は (ii) を満たすが (i) を満たさない。一般の兄弟は (i) を満たすが (ii) を満たさない。

(ii) を層の欄に直接書くと非可述になる（`Qok (j+1) 0` の定義が `Qok j'` を
すべての `j'` について参照する）。`APd` / `TwoOk` でうまくいったのは
「先に定義済みの層での全レベル条件」を書く逃げ道だが、それだと
**下の層に対する全レベル性しか出ない**。上の層に移すには上の層の枠木が
下の層で良いことが要り、それが壁そのもの（1 の枠木 `two nil nil` を
下の層の `(j, 0)` に置く = `Pk j 0 (two nil nil)`）。

試した設計は通算 12 通り。全部この 1 点で止まる。

## 欲しいもの

次のどれか。

1. `QPayPair` の直接証明。荷の近似列 `twoIt nil (pay X Y') k` を
   左兄弟にしない別の書き方があればよい。

2. (i) と (ii) を同時に満たす左兄弟の族。
   `nil` から `Wl ↦ two Wl (pay X Y)` で閉じていて、かつ全レベルで置けるもの。
   全レベル性は `Qk (j+1) 0 (pay X Y)` を全 `j` で要求するので、
   X 自身が全レベルで良いときには回る。困るのは X が一般のとき
   （`Qk_pay` の内部で 1 の記録の鎖 `itJ T k U` に荷を吊るす所で、
    `U` は文脈の枠木なので全レベルではない）。

3. BM4 の展開規則の側から「左兄弟の良さがレベルを跨ぐ」理由。
   それが付けば (ii) を層の条件から外せる。

## 参考

Lean のファイルは `lean/Small.lean`（約 60000 行、緑、`sorryAx` なし）。
設計の試行錯誤は `notes.md` の追記149〜170 に全部書いてある。
