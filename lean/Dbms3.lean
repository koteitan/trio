/-
3 行 DBMS の器（骨組み）。

BMS 側（`Trio.lean` の `ST_TS`, `oper`）はそのまま使う。DBMS は**展開規則が
BMS と完全に同一**で、違うのは標準形の対角だけ、というのが 2 行（`Dbms.lean`）
と同じ設計である。

    対角 diag[x][y]   BMS: x               DBMS: max(x - y, 0)

いま対象にしているのは z < 2 の断片なので、BMS 側の対角は z を 1 で頭打ちした
`diagSeqT 0 v = ((j, j, min j 1))_{j=0..v}` である。その像を実測すると

    b2d3 (0,0,0)(1,1,1)                     = (0,0,0)(1,0,0)(2,1,0)(3,2,1)
    b2d3 (0,0,0)(1,1,1)(2,2,1)              = (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,3,1)
    b2d3 (0,0,0)(1,1,1)(2,2,1)(3,3,1)       = (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,3,1)(5,4,1)

（`tools/dbms/rows3.py` の `b2d3`, v = 0..20 で確認）。つまり DBMS 側の対角も
**z を 1 で頭打ちした** `((j, j-1, min (j-2) 1))_{j=0..v}` である。素の
`(j, j-1, j-2)` は z ≥ 2 に出てしまうので、この断片の対角にはならない。

頭打ち対角が「本物の DBMS 対角の一手展開」であることも実測ずみ
（`core.expand`）:

    D5 = (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,3,2)      … 5 列の素の DBMS 対角
    D5⟦n⟧ = ddiagSeqT (n + 2)                     (n ≥ 1)

BMS 側で `diagSeqT 0 v` が 3 列のトリオ対角の一手展開なのと同じ形である。
`core.isstd(ddiagSeqT v, 'DBMS')` も v = 0..9 で真。

## この器が固定するもの

* `ST_D3` : 3 行 DBMS の標準形（対角 + 展開の 2 構成子）。
* `ReindexT1` : 2 行の `ReindexD`（`DbmsStd.lean:1557`）の 3 行版。
  **性質 R（相手が `A⟦n'⟧` であること）は 3 行では偽**（`tools/dbms/NOTES.md`
  「性質 R（ReindexD）は 3 行で偽」）。降下が本当に要求しているのは
  「相手が BMS 標準形 `B` であること」だけなので、そこまで緩めてある。
* `ST_D3_descend` / `ST_D3_conv3` : `DbmsStd.lean:1578-1613` の写経。
  `A⟦n'⟧` を `B` に置き換えると `oper_mono` の行が仮定 `translate (A⟦n⟧) ≤o
  translate B` に吸収されて消える。

`conv3`（BMS -> DBMS の変換器、Python では `tools/dbms/rows3.py` の `b2d3`）は
§1-§7 では**関数変数として抽象化**してある。Python 側が保証すべき命題は
`ReindexT1` と `ConvDiagT3` の 2 つだけになる。

## §8 以降（2026-08-27 に足した分）

`conv3` の Lean 実装 `Conv3.conv3` / `Conv3.b2d3` を書いた（§8）。**縮約こみ**、
つまり `rows3.py` の `conv3` 設計 v11 まるごとの写経である。Python との
突き合わせ（`#guard` = 実際に両方を計算して比べる）:

    <=6 列の BMS 3 行 z<2 標準形 **8387 個を全数**        食い違い 0（149 秒）
    7 列（68895 個）のうち **縮約が発火する 294 個ぜんぶ**
      ＋ 無作為 5000 個                                    食い違い 0（74 秒）

そのうえで `ConvDiagT3 Conv3.b2d3` を**証明した**（§9, §10）。
残るのは `ReindexT1` ただ 1 つ（`ST_D3_b2d3`）。
-/
import Core
import Decrease
import Seqlex
import Wset
import Final

namespace TRIO

open Three
open Classical

/-! ## 0. `≤o` の小道具（2 行側の `DbmsStd.lean:53-63` の TRIO 版） -/

theorem ole_refl (x : Three) : x ≤o x := Or.inr rfl

theorem ole_trans {x y z : Three} (hxy : x ≤o y) (hyz : y ≤o z) : x ≤o z := by
  rcases hxy with h | rfl
  · exact Or.inl (olt_ole_trans h hyz)
  · exact hyz

theorem ole_olt_trans {x y z : Three} (hxy : x ≤o y) (hyz : y <o z) : x <o z := by
  rcases hxy with h | rfl
  · exact olt_trans h hyz
  · exact hyz

/-! ## 1. 3 行 DBMS の対角と標準形 -/

/-- DBMS の 3 行対角の第 `j` 列 `(j, j-1, min (j-2) 1)`（ℕ の切り捨て引き算）。
z を 1 で頭打ちしてあるのは、いま扱っているのが z < 2 の断片だから。 -/
def ddcolT (j : ℕ) : ℕ × ℕ × ℕ := (j, j - 1, min (j - 2) 1)

/-- DBMS の 3 行対角 `(0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,3,1)…(v,v-1,1)`。 -/
def ddiagSeqT (v : ℕ) : TrioSeq := (List.range (v + 1)).map ddcolT

example : ddiagSeqT 0 = [(0, 0, 0)] := by decide
example : ddiagSeqT 6 =
    [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,1), (6,5,1)] := by decide

/-- 3 行 DBMS の標準形: 対角から展開 `M⟦n⟧`（`n ≥ 1`）で到達できるもの。
展開 `oper` は BMS と同一のもの（`Trio.lean`）を使う。 -/
inductive ST_D3 : TrioSeq → Prop where
  | diag (v : ℕ) : ST_D3 (ddiagSeqT v)
  | oper {M : TrioSeq} {n : ℕ} : ST_D3 M → 1 ≤ n → ST_D3 (M⟦n⟧)

/-! ## 2. 変換器に課す 2 つの命題

`conv3 : TrioSeq → TrioSeq` は「BMS 3 行標準形 -> DBMS 3 行行列」の変換器。
Lean の実装はまだ無いので関数変数のまま置く。 -/

/-- **対角の像**（帰納法の底）。実測（`tools/dbms/rows3.py` の `b2d3`）:

    conv3 (diagSeqT 0 0) = ddiagSeqT 0
    conv3 (diagSeqT 0 v) = ddiagSeqT (v + 2)     (v ≥ 1)

像は入力より 2 列長い。2 行では 1 列長かった（`conC_diagSeq`）。 -/
def ConvDiagT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ v : ℕ, conv3 (diagSeqT 0 v) = if v = 0 then ddiagSeqT 0 else ddiagSeqT (v + 2)

/-- **ReindexT1** — 2 行の `ReindexD` の 3 行版。

`A` が BMS 3 行標準形で長さ 2 以上、`n ≥ 1` のとき、DBMS の添字 `m ≥ 1` と
**ある BMS 標準形 `B`** があって

    translate (A⟦n⟧) ≤o translate B     … 基本列に追い越されない（上）
    translate B <o translate A          … ちゃんと降りている（下）
    (conv3 A)⟦m⟧ = conv3 B              … 像は展開で閉じている

2 行版は `B = A⟦n'⟧`（`n ≤ n'`）だったが、**3 行ではそれが偽**である
（`tools/dbms/NOTES.md`「性質 R（ReindexD）は 3 行で偽（2026-08-27, 確定）」。
反例 `M = (0,0,0)(1,1,1)(2,1,0)(3,0,0)` は `f(M)⟦m⟧` と `f(M⟦n⟧)` が末尾 1 列
の行 1 で永久にすれ違う）。その反例でも `B_m = (0,0,0)(1,1,1)(2,1,0)^m
(1,1,0)(2,2,1)(3,2,0)^m` を取れば `ReindexT1` は満たされる（m = 1..6 で確認）。

`ST_D3_descend` が `ReindexD` を使う 2 か所のうち、DBMS 側の等号は落とせないが
BMS 側の `n ≤ n'` は `≤o` に翻訳されてからしか使われない。だから相手は
`A⟦n'⟧` である必要が無い、というのがこの緩和の根拠。 -/
def ReindexT1 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {A : TrioSeq}, ST_TS A → 1 < A.length → ∀ n : ℕ, 1 ≤ n →
    ∃ (m : ℕ) (B : TrioSeq), 1 ≤ m ∧ ST_TS B ∧
      translate (A⟦n⟧) ≤o translate B ∧
      translate B <o translate A ∧
      (conv3 A)⟦m⟧ = conv3 B

/-- `ConvDiagT3` から帰納法の底が出る。 -/
theorem ST_D3_conv3_diag {conv3 : TrioSeq → TrioSeq} (hd : ConvDiagT3 conv3) (v : ℕ) :
    ST_D3 (conv3 (diagSeqT 0 v)) := by
  rw [hd v]
  by_cases h : v = 0
  · simp only [h, if_true]; exact ST_D3.diag 0
  · simp only [if_neg h]; exact ST_D3.diag (v + 2)

/-! ## 3. 長さ 1 の標準形は最小（`DbmsStd.lean:68` の TRIO 版） -/

/-- `[(0,0,0)]` より真に小さい BMS 3 行標準形はない。 -/
theorem not_olt_len_one_T {M A : TrioSeq} (hM : ST_TS M) (hA : A.length ≤ 1)
    (hAst : ST_TS A) (h : translate M <o translate A) : False := by
  have h1 : A = [(0, 0, 0)] := Wset.stts_len_one hAst (by
    have := stps_len_pos hAst; omega)
  subst h1
  have hA0 : translate [((0 : ℕ), (0 : ℕ), (0 : ℕ))] = P 0 0 Z Z := by
    rw [translate]; simp
  obtain ⟨p, R, rfl⟩ := List.exists_cons_of_ne_nil (Wset.stts_ne_nil hM)
  rw [hA0, translate] at h
  rcases olt_P_P.mp h with h | ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩
  · omega
  · omega
  · exact not_olt_Z _ h
  · exact not_olt_Z _ h

/-! ## 4. 対角は標準形の中で共終（`DbmsStd.lean:87` の TRIO 版） -/

/-- どの BMS 3 行標準形も、ある z 頭打ち対角以下。 -/
theorem diag_cofinal_T {M : TrioSeq} (hM : ST_TS M) :
    ∃ v, translate M ≤o translate (diagSeqT 0 v) := by
  induction hM with
  | diag v => exact ⟨v, ole_refl _⟩
  | @oper N n hN hn ih =>
      obtain ⟨v, hv⟩ := ih
      by_cases hL : 1 < N.length
      · exact ⟨v, ole_trans (Or.inl (m_step_decreases hL hn)) hv⟩
      · have hs : N⟦n⟧ = N := oper_eq_self_of_short n (by omega)
        rw [hs]; exact ⟨v, hv⟩

/-! ## 5. 降下（`DbmsStd.lean:1578` の写経） -/

/-- 降下の本体: 標準形の像 `conv3 A` が DBMS 標準形なら、`A` 以下の
BMS 標準形の像もすべて DBMS 標準形。

`A` についての整礎帰納法。`wf` は `Final.lean` の `wf_olt_ST_TS_holds`
（`TowerGraft2` と `TowerExp` の 2 核が残っている）でも、それを閉じた後の
無条件版でも良いように、仮定として受け取る。

2 行版との差は 1 行だけ: `oper_mono hnn` と `ole_trans hMn hmono` の 2 行が、
`ReindexT1` が直に渡してくる `translate (A⟦n⟧) ≤o translate B` に吸収されて
`ole_trans hMn hAnB` の 1 行になる。 -/
theorem ST_D3_descend
    (wf : WellFounded
      (fun a b : TrioSeq => ST_TS a ∧ ST_TS b ∧ translate a <o translate b))
    {conv3 : TrioSeq → TrioSeq} (H : ReindexT1 conv3) :
    ∀ A : TrioSeq, ST_TS A → ST_D3 (conv3 A) →
      ∀ M : TrioSeq, ST_TS M → translate M ≤o translate A → ST_D3 (conv3 M) := by
  intro A
  induction A using wf.induction with
  | _ A ih =>
    intro hA hSD M hM hle
    rcases hle with hlt | heq
    · -- `translate M <o translate A`: 一段降ろす
      have hL : 1 < A.length := by
        by_contra hL
        exact not_olt_len_one_T hM (by omega) hA hlt
      obtain ⟨n, hn, hMn⟩ := trio_cofinality hA hM hlt
      obtain ⟨m, B, hm, hB, hAnB, hBA, heqC⟩ := H hA hL n hn
      have hSD' : ST_D3 (conv3 B) := by
        rw [← heqC]; exact ST_D3.oper hSD hm
      exact ih B ⟨hB, hA, hBA⟩ hB hSD' M hM (ole_trans hMn hAnB)
    · -- `translate M = translate A`: `M = A`
      have hMA : M = A := by
        by_contra hne
        rcases seqlex_total M A with he | hs | hs
        · exact hne he
        · exact olt_irrefl _ (heq ▸ (olt_ST_iff_seqlex hM hA hne).2 hs)
        · exact olt_irrefl _ (heq ▸ (olt_ST_iff_seqlex hA hM (Ne.symm hne)).2 hs)
      rw [hMA]; exact hSD

/-! ## 6. 主定理 -/

/-- **像は DBMS の 3 行標準形**（`ReindexT1` と `ConvDiagT3` を仮定）。 -/
theorem ST_D3_conv3
    (wf : WellFounded
      (fun a b : TrioSeq => ST_TS a ∧ ST_TS b ∧ translate a <o translate b))
    {conv3 : TrioSeq → TrioSeq} (H : ReindexT1 conv3) (hd : ConvDiagT3 conv3)
    {M : TrioSeq} (hM : ST_TS M) : ST_D3 (conv3 M) := by
  obtain ⟨v, hv⟩ := diag_cofinal_T hM
  exact ST_D3_descend wf H (diagSeqT 0 v) (ST_TS.diag v) (ST_D3_conv3_diag hd v) M hM hv

/-! ## 7. いまの仮定をぜんぶ並べた形 -/

/-- 3 行の器を、現時点で残っている仮定を全部明示して組み立てたもの。

* `h2`, `he` … BMS 側の整礎性に残る 2 核（`Final.lean` の
  `wf_olt_ST_TS_holds`）。3 行 BMS の停止性そのものの残核で、
  DBMS とは無関係。
* `H`  … `ReindexT1`（変換器の像が展開で閉じ、順序でも挟まれる）。
* `hd` … `ConvDiagT3`（対角の像が DBMS 対角）。

`H` と `hd` の 2 つが、Python 側（`tools/dbms/rows3.py` の `b2d3`）が
保証すべきものの全部である。 -/
theorem ST_D3_conv3_holds (h2 : Wset.TowerGraft2) (he : Wset.TowerExp)
    {conv3 : TrioSeq → TrioSeq} (H : ReindexT1 conv3) (hd : ConvDiagT3 conv3)
    {M : TrioSeq} (hM : ST_TS M) : ST_D3 (conv3 M) :=
  ST_D3_conv3 (wf_olt_ST_TS_holds h2 he) H hd hM


/-! ## 8. 変換器 `conv3` の Lean 実装

`tools/dbms/rows3.py` の `conv3`（設計 v11）の写経。**縮約こみ**である。

Python の `conv3` は状態 `st` を**破壊的に**持ち回るので、Lean では
`TrioSeq × St` を返して線形に渡す。`cA` を先に走らせて、その状態で `cU`,
`cR`, `cB` を走らせる、という順序が Python の副作用の順序に対応する。

縮約には `conv3` と `conv_resid` の**相互再帰**が要る。`conv_resid` は残余の
先頭ブロックを丸ごと `conv3` に渡すので列数が減らないことがあり、素朴な
「列数」では停止しない。尺度を `conv3 -> 2 * M.length`,
`convResid -> 2 * rest.length + 1` に取ると 1 本の ℕ で足りる:

    conv3 M    -> conv3 A/U/Bq     列数が真に減る          2a   < 2m
    conv3 M    -> convResid rest2  列数が真に減る          2r+1 < 2m
    convResid  -> conv3 head       列数は減らなくてよい    2h   < 2r+1
    convResid  -> convResid tail   列数が真に減る          2t+1 < 2r+1

`A`/`B` は `takeWhile`/`dropWhile` のままだが、縮約の断片（`U`, `Aq`, `Bq`,
`rest2`）は `take`/`drop` と長さ `deepGe` で作ってある。そうすると長さの上界が
`List.length_take` / `List.length_drop` だけで出て、`decreasing_by` が
`omega` 一発で閉じる。

**Python との突き合わせ**: <=6 列の標準形 8387 個を全数 `#guard` して食い違い 0
（149 秒）。7 列は「縮約が発火する 294 個ぜんぶ ＋ 無作為 5000 個」で 0（74 秒）。
下にはそのうちの一部（<=6 列で縮約が発火するもの全部と、6/7 列の抜き取り）を
残してある。

縮約が発火するのは稀で、<=7 列 77282 個のうち 338 個（0.44%）だけ
（`rows3.b2d3n` の第 2 成分 `nc` で数えた: 5 列 5 / 6 列 39 / 7 列 294）。 -/

namespace Conv3

/-- 列。 -/
abbrev Col := ℕ × ℕ × ℕ

/-- 段の表 `L` の 1 項
`(深い側の行 1, その行 2, force1, 浅い側の行 1, 兄弟だけが使える深い側)`。

第 5 項は v13 の `sibL`（`rows3.py` の `L` の第 5 要素）。行 1 の影を立てた柱が
**兄弟にだけ**渡す深い側である。Python では第 5 要素が「無い」4 つ組があって、
そのとき `base_sd = e[0]` と読む約束なので、Lean では「無い」を
**第 5 項 = 第 1 項**で表す。 -/
abbrev Lent := ℕ × ℕ × Bool × ℕ × ℕ

/-- 引数に渡す表 `LA` を作るときの潰し（Python の `tuple(t[:4] for t in LA)`）。
第 5 項を第 1 項に戻す＝「兄弟の深い側は子には渡さない」。 -/
def lentTrunc (t : Lent) : Lent := (t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.1)

/-- 線形に持ち回る状態（Python の辞書 `st`）。 -/
structure St where
  /-- 祖先の鎖（深さ -> (行 1, 行 2)）。 -/
  ST : List (ℕ × ℕ)
  /-- 直前の分岐列の選択。`0` 浅い / `1` 深い / `2` まだ無い（Python の `None`）。 -/
  prev : ℕ
  /-- もとの深さ -> 像の深さ。 -/
  dmap : List ℕ
  /-- もとの行列まるごと。 -/
  Mo : TrioSeq
  /-- 縮約が発火した回数。 -/
  nc : ℕ
deriving Repr, DecidableEq

/-- `Lat L k`: 段の表の第 `k` 項。表の外は 1 段ずつ伸ばして読む。 -/
def Lat (L : List Lent) (k : ℕ) : Lent :=
  match L[k]? with
  | some e => e
  | none =>
      match L.getLast? with
      | none => (0, 0, false, 0, 0)
      | some a =>
          (a.1 + (k + 1 - L.length), a.2.1, false, a.2.2.2.1 + (k + 1 - L.length),
            a.1 + (k + 1 - L.length))

/-- `padL L v`: 長さ `v` まで `Lat` で埋めてから切る。 -/
def padL (L : List Lent) (v : ℕ) : List Lent :=
  if L.length < v then (List.range v).map (fun k => Lat L k) else L.take v

/-- 深さ `x` に行 1 が `w` の柱を置けるか。 -/
def okPlace (ST : List (ℕ × ℕ)) (x w : ℕ) : Bool :=
  if w = 0 then true
  else if x ≤ w then false
  else
    match (ST.take x).reverse.find? (fun e => decide (e.1 < w)) with
    | some e => e.1 == w - 1
    | none => false

/-- `fit` の本体（燃料つき）。 -/
def fitAux (ST : List (ℕ × ℕ)) (w : ℕ) : ℕ → ℕ → Option ℕ
  | _, 0 => none
  | x, (k + 1) => if okPlace ST x w then some x else fitAux ST w (x + 1) k

/-- 深さ `d` 以上で行 1 が `w` になれる最小の深さ。 -/
def fit (ST : List (ℕ × ℕ)) (d w : ℕ) : Option ℕ :=
  fitAux ST w d (ST.length + 1 - d)

/-- 分岐列 `(a,1,0)`（`a ≥ 2`）。浅い／深いを選ぶのはこの型だけ。 -/
def isBranch (c : Col) : Bool := c.2.1 == 1 && c.2.2 == 0 && decide (2 ≤ c.1)

/-- 次の列がこの加算ユニットを閉じるか。 -/
def closesUnit : Option Col → Bool
  | none => true
  | some c => decide (c.1 ≤ 1) && c.2.2 == 0

/-- 「x w」の柱 `(k,0,0)`（`k ≥ 1`）。 -/
def isWCol : Option Col → Bool
  | none => false
  | some c => c.2.1 == 0 && decide (1 ≤ c.1)

/-- `par0` の本体（`q = x-1` から下へ）。 -/
def par0Aux (m : TrioSeq) (w : ℕ) : ℕ → Option ℕ
  | 0 => none
  | (q + 1) => if (m.getD q (0,0,0)).1 < w then some q else par0Aux m w q

/-- 柱 `x` の行 0 の親の添字。 -/
def par0 (m : TrioSeq) (x : ℕ) : Option ℕ := par0Aux m (m.getD x (0,0,0)).1 x

/-- `x` の直前のアンカーの添字（無ければ 0）。 -/
def hiB (m : TrioSeq) : ℕ → ℕ
  | 0 => 0
  | (q + 1) =>
      let c := m.getD q (0,0,0)
      if c.1 = c.2.1 ∧ 1 ≤ c.1 then q else hiB m q

/-- `x` の属するブロックに行 2 を使う柱があるか（W_(w^2) 系の目印）。 -/
def hiBlock (m : TrioSeq) (x : ℕ) : Bool :=
  ((List.range x).drop (hiB m x + 1)).any
    (fun z => decide (0 < (m.getD z (0,0,0)).2.2))

/-- `isRepeat` の本体（周期 `L = k+1` を下へ）。 -/
def isRepeatAux (m : TrioSeq) (x : ℕ) : ℕ → Bool
  | 0 => false
  | (k + 1) =>
      let l := k + 1
      ((m.drop (x + 1 - 2 * l)).take l == (m.drop (x + 1 - l)).take l)
        || isRepeatAux m x k

/-- `m[..x]` の末尾が、その直前の同じ長さの区間の逐語コピーか。 -/
def isRepeat (m : TrioSeq) (x : ℕ) : Bool := isRepeatAux m x ((x + 1) / 2)

/-- `(a,2,1)(a,2,0)(a,1,0)` の直後が `(1,1,1)` なら段を上げずに閉じる。 -/
def closesHiUnit (c : Col) (nxt pv pv2 : Option Col) (hi rep : Bool) : Bool :=
  hi && !rep && nxt == some (1, 1, 1) && pv == some (c.1, 2, 0)
    && pv2 == some (c.1, 2, 1)

/-- `wchainHead` の本体（添字を `off` から 1 つずつ下げる。燃料 = その添字）。 -/
def wchainHeadAux (m : TrioSeq) (off : ℕ) : ℕ → Option ℕ
  | 0 => none
  | (j + 1) =>
      let c := m.getD j (0, 0, 0)
      if isWCol (some c) then
        (if ((List.range (off + 1)).drop (j + 1)).all
              (fun t => decide (c.1 < (m.getD t (0, 0, 0)).1)) then some j else none)
      else if c.1 = 0 then none
      else wchainHeadAux m off j

/-- v13 `wchain`（`rows3.py` の `wchain_head`）。`off` から後ろへ「x w」の柱
`(k,0,0)` をさがす。ただし**その柱から `off` までの柱がぜんぶ行 0 > k**
（＝その柱の子孫）でなければならない。行 0 が 0 の柱（新しい加算項の頭）に
当たったら諦める。

直前 1 本だけを見る `after_w` を、写しの頭まで届くように広げたもの。 -/
def wchainHead (m : TrioSeq) (off : ℕ) : Option ℕ := wchainHeadAux m off off

/-- v13 `sib_anchbefore`（`rows3.py` の `sib_ok`）。兄弟から渡された深い側
`base_sd` を使ってよいのは、この柱より前にアンカー `(1,1,0)` が 1 本も無い
ときだけ。アンカーは行 1 の新しい加算ユニットの頭なので、「行 1 の最初の
ユニットの中でだけ、影の深さは兄弟に効く」という読み方になる。 -/
def sibOk (m : TrioSeq) (off : ℕ) : Bool :=
  !((List.range off).any (fun j => m.getD j (0, 0, 0) == ((1, 1, 0) : Col)))

/-! ### 縮約の道具（`rows3.py` の `units_split` / `copy_shift` / `contrPre`） -/

/-- アンカー（新しい加算ユニットの頭）。 -/
def ANCHOR : Col := (1, 1, 0)

/-- 「後ろにユニットを閉じない列がある」を表す番兵。 -/
def NOTLAST : Col := (2, 2, 0)

/-- 行 0 が `a` より深い先頭部分の長さ。 -/
def deepLen (a : ℕ) : TrioSeq → ℕ
  | [] => 0
  | q :: r => if a < q.1 then deepLen a r + 1 else 0

/-- `units_split` の切れ目（燃料つき）。 -/
def unitsLenAux (p0 : ℕ) (qlab : ℕ × ℕ) (B : TrioSeq) : ℕ → ℕ → ℕ
  | k, 0 => k
  | k, (f + 1) =>
      if k < B.length then
        let c := B.getD k (0, 0, 0)
        if c.1 ≠ p0 then k
        else if (c.2.1, c.2.2) = qlab then k
        else unitsLenAux p0 qlab B (k + 1 + deepLen p0 (B.drop (k + 1))) f
      else k

/-- `B` の先頭から「深さ `p0` の柱＋その引数ブロック」を、段の対が `qlab` に
等しい柱に出会うまで取ったときの長さ。 -/
def unitsLen (p0 : ℕ) (qlab : ℕ × ℕ) (B : TrioSeq) : ℕ :=
  unitsLenAux p0 qlab B 0 B.length

/-- 写し（深さ +1、行 1 は条件つきで +e）。分岐列の浅い／深いは同じ状態機械で
1 本ずつ決め直す。 -/
def copyShift : TrioSeq → ℕ → ℕ → ℕ → Option Col → TrioSeq
  | [], _, _, _, _ => []
  | c :: rest, e, ps0, prev0, nxtAfter =>
      let nxt : Option Col := match rest with | q :: _ => some q | [] => nxtAfter
      let prev1 := if c = ANCHOR then 0 else prev0
      let sh := (prev1 == 0) || closesUnit nxt
      let dl :=
        if isBranch c then (if sh then 0 else (if ps0 < c.2.1 then e else 0))
        else (if ps0 < c.2.1 then e else 0)
      let prev2 := if isBranch c then (if sh then 0 else 1) else prev1
      (c.1 + 1, c.2.1 + dl, c.2.2) :: copyShift rest e ps0 prev2 nxtAfter

/-- 写しの先頭（`[p] ++ A ++ U` の写し）。 -/
def contrPre (p : Col) (U A : TrioSeq) (e ps0 prev0 : ℕ) (nxtAfter : Option Col) : TrioSeq :=
  copyShift (p :: (A ++ U)) e ps0 prev0 nxtAfter

/-- もとの深さ `k` が像で何段目になるか。 -/
def dmapAt (dm : List ℕ) (k : ℕ) : ℕ :=
  if dm = [] then k
  else if k < dm.length then dm.getD k 0
  else (dm.getLastD 0) + (k - dm.length + 1)

/-- 対の**辞書式**の `≥`（Python のタプル比較。Mathlib の `Prod` の順序は
成分ごとなので、そのままでは使えない）。 -/
def lexGe (a b : ℕ × ℕ) : Bool := decide (b.1 < a.1) || (decide (a.1 = b.1) && decide (b.2 ≤ a.2))

/-- 行 0 が `a` 以上で続く先頭部分の長さ。 -/
def deepGe (a : ℕ) : TrioSeq → ℕ
  | [] => 0
  | q :: r => if a ≤ q.1 then deepGe a r + 1 else 0

/-- 縮約の候補を 1 つの `e` について探す。見つかれば `(kU, kpre, na)`
（写しの長さ、写しの先頭の長さ、写しの「次の列」）。`rows3.py` の `lad0` の枝。 -/
def contrOne (p : Col) (A B : TrioSeq) (ps : ℕ × ℕ) (v s2 prev0 e : ℕ) :
    Option (ℕ × ℕ × Col) :=
  let qlab : ℕ × ℕ := (ps.1 + e, ps.2)
  let kU := unitsLen p.1 qlab B
  match B.drop kU with
  | [] => none
  | q :: r2 =>
      if (q.2.1, q.2.2) ≠ qlab ∨ q.1 ≠ p.1 then none
      else
        let U := B.take kU
        let Aq := r2.take (deepGe (q.1 + 1) r2)
        let blk := p :: (A ++ U)
        let tryNa : Col → Option (TrioSeq × Col) := fun na =>
          let pre := contrPre p U A e ps.1 prev0 (some na)
          if Aq.take pre.length = pre then some (pre, na) else none
        match (match tryNa q with | some x => some x | none => tryNa NOTLAST) with
        | none => none
        | some (pre, na) =>
            let lastB := blk.getLastD (0, 0, 0)
            let lastP := pre.getLastD (0, 0, 0)
            let deepEnd := isBranch lastB && decide (lastB.2.1 < lastP.2.1)
            let rest2 := Aq.drop pre.length
            match rest2 with
            | [] => if e ≠ 0 ∧ deepEnd = true then some (kU, pre.length, na) else none
            | c :: _ =>
                if c.1 < p.1 + 1 then none
                else if c.1 = p.1 + 1 ∧ lexGe (c.2.1, c.2.2) (v + e, s2) = true ∧ e = 0 then
                  none
                else some (kU, pre.length, na)

/-- `e = 0` を先に、だめなら `e = 1` を試す。返り値は `(e, kU, kpre, na)`。 -/
def contrFind (p : Col) (A B : TrioSeq) (ps : ℕ × ℕ) (v s2 prev0 : ℕ) :
    Option (ℕ × ℕ × ℕ × Col) :=
  match contrOne p A B ps v s2 prev0 0 with
  | some (kU, kp, na) => some (0, kU, kp, na)
  | none =>
      match contrOne p A B ps v s2 prev0 1 with
      | some (kU, kp, na) => some (1, kU, kp, na)
      | none => none

/-- 兄弟が無ければ縮約は起きない。 -/
@[simp] theorem contrOne_nil (p : Col) (A : TrioSeq) (ps : ℕ × ℕ) (v s2 prev0 e : ℕ) :
    contrOne p A [] ps v s2 prev0 e = none := by
  simp [contrOne]

@[simp] theorem contrFind_nil (p : Col) (A : TrioSeq) (ps : ℕ × ℕ) (v s2 prev0 : ℕ) :
    contrFind p A [] ps v s2 prev0 = none := by
  simp [contrFind]

mutual

/-- BMS 3 行 (z<2) -> DBMS 3 行。`rows3.py` の `conv3`（設計 v13）の写経。

Python の `conv3` は状態 `st` を**破壊的に**持ち回るので、Lean では
`TrioSeq × St` を返して線形に渡す。`cA` を先に走らせて、その状態で `cU`,
`cR`, `cB` を走らせる、という順序が Python の副作用の順序に対応する。

停止性の尺度は `2 * M.length`（`convResid` は `2 * rest.length + 1`）。
`convResid` は残余の先頭ブロックを丸ごと `conv3` に渡すので列数が減らない
ことがあり、それを「同じ列数なら `conv3` のほうが小さい」で受ける。 -/
def conv3 (M : TrioSeq) (d : ℕ) (L : List Lent) (F : List Bool)
    (ps pw : ℕ × ℕ) (first force : Bool) (st : St) (nx : Option Col) (off : ℕ) :
    TrioSeq × St :=
  match M with
  | [] => ([], st)
  | p :: r =>
    let v := p.2.1
    let s2 := p.2.2
    let A := r.takeWhile (fun q => decide (p.1 < q.1))
    let B := r.dropWhile (fun q => decide (p.1 < q.1))
    let ent := Lat L (v - 1)
    let base_d := if v = 0 then 0 else ent.1 + 1
    let base_s := if v = 0 then 0 else ent.2.2.2.1 + 1
    -- v13 sibL: 兄弟だけが使える深い側（第 5 項）。無いときは第 1 項＝`base_d`。
    let base_sd := if v = 0 then 0 else ent.2.2.2.2 + 1
    let pl2 := if v = 0 then 0 else ent.2.1
    let force1 := if v = 0 then false else ent.2.2.1
    let first1 := F.getD v true
    let bp : ℕ × ℕ :=
      if isBranch p then
        -- v13 sibL: 深い側の候補は、兄弟から渡ってきた `base_sd` を使ってよければ
        -- それ。門は「浅い側 != 深い側の候補」で開く（`base_d` ではなく `deep`）。
        let deep := if (base_sd != base_d) && sibOk st.Mo off then base_sd else base_d
        if base_s != deep then
          let nxt : Option Col := match r with | q :: _ => some q | [] => nx
          let Mo := st.Mo
          let pv : Option Col := if 1 ≤ off then some (Mo.getD (off - 1) (0,0,0)) else none
          let pv2 : Option Col := if 2 ≤ off then some (Mo.getD (off - 2) (0,0,0)) else none
          let onx : Option Col :=
            if off + 1 < Mo.length then some (Mo.getD (off + 1) (0,0,0)) else none
          let hi := hiBlock Mo off
          let sh0 := (st.prev == 0) || closesUnit nxt
          let sh1 :=
            if (st.prev == 1) && isWCol pv && closesUnit onx then
              let pnt := decide (0 < off) && (par0 Mo (off - 1) == some 0)
              !(hi && !pnt)
            else if (st.prev == 1) && closesUnit onx then
              -- v13 wchain: `after_w` の窓を「この写しの頭まで」広げる。
              -- 判定式は `after_w` と同じで、親を見る柱だけ `(k,0,0)` 本人にする。
              -- `after_w` が発火するときはそちらが優先（この `else if`）。
              match wchainHead Mo off with
              | some j => !(hi && !(par0 Mo j == some 0))
              | none => sh0
            else sh0
          let sh := sh1 || closesHiUnit p onx pv pv2 hi (isRepeat Mo off)
          if sh then (base_s, 0) else (deep, 1)
        else (deep, st.prev)
      else (base_d, st.prev)
    let base := bp.1
    let lad1 := first1 && (s2 == pl2 + 1) && (decide (base ≤ s2) || force1)
    let e1 := if lad1 then base + 1 else (if 0 < s2 ∧ base ≤ s2 then s2 + 1 else base)
    let e2 := s2
    let h1 := if lad1 then base else e1
    let lad0 := first && (v == ps.1 + 1) && (decide (d ≤ h1) || force)
    let ST1 := if lad0 then st.ST.take d ++ [(pw.1, pw.2)] else st.ST
    let dd0 := if lad0 then d + 1 else (fit st.ST d h1).getD (max d st.ST.length)
    let ST2 := if lad1 then ST1.take dd0 ++ [(base, pl2)] else ST1
    let dd1 := if lad1 then dd0 + 1 else dd0
    let dd2 := if okPlace ST2 dd1 e1 then dd1 else (fit ST2 dd1 e1).getD dd1
    let cols : TrioSeq :=
      (if lad0 then [(d, pw.1, pw.2)] else []) ++
        (if lad1 then [(dd0, base, pl2)] else []) ++ [(dd2, e1, e2)]
    let st1 : St :=
      { ST := ST2.take dd2 ++ [(e1, e2)], prev := bp.2,
        dmap := st.dmap.take p.1 ++ [dd2], Mo := st.Mo, nc := st.nc }
    let fc := (!lad1) && first1 && (s2 == pl2)
    let f0 := (!lad0) && first && (v == ps.1) && (s2 == ps.2)
    let Lb :=
      if (e1 == base + 1) && decide (1 ≤ v) then
        padL L (v - 1) ++ [(base, pl2, false, (Lat L (v - 1)).2.2.2.1, base)]
      else L
    -- v13 sibL: 第 5 項は**子には渡さない**（渡すとアンカーを素通りして
    -- 次の加算ユニットまで深い綴りが届く）。Python の `t[:4]` に対応。
    let LA := (padL Lb v).map lentTrunc ++ [(e1, s2, fc, e1, e1)]
    let FA := F.take v ++ [false]
    match (if lad0 then contrFind p A B ps v s2 bp.2 else none) with
    | some (e, kU, kp, na) =>
        let U := B.take kU
        let q := (B.drop kU).headD (0, 0, 0)
        let r2 := (B.drop kU).tail
        let Aq := r2.take (deepGe (q.1 + 1) r2)
        let Bq := r2.drop (deepGe (q.1 + 1) r2)
        let rest2 := Aq.drop kp
        let oU := off + 1 + A.length
        let oq := oU + U.length
        let Lr :=
          padL L v ++ [if e = 0 then (e1, s2, fc, e1, e1) else (base, pl2, fc, base, base)]
        let rA := conv3 A (dd2 + 1) LA FA (v, s2) (e1, e2) true false st1
                    (match U with | u :: _ => some u | [] => some na) (off + 1)
        let rU := conv3 U (d + 1) L FA (v, s2) (e1, e2) false false rA.2 (some na) oU
        let rd := if rest2 = [] ∨ (rest2.headD (0,0,0)).1 = p.1 + 1 then d + 1 + e
                  else dmapAt rU.2.dmap ((rest2.headD (0,0,0)).1 - 1)
        let rR := convResid rest2 rd Lr (v, s2) (e1, e2) rU.2
                    (match Bq with | b :: _ => some b | [] => nx) (oq + 1 + kp)
        let rB := conv3 Bq d L FA (v, s2) (e1, e2) false false rR.2 nx (oq + 1 + Aq.length)
        (cols ++ rA.1 ++ rU.1 ++ rR.1 ++ rB.1,
          { rB.2 with nc := rB.2.nc + 1 })
    | none =>
        -- v13 sibL: 行 1 の影を立てたら、そのあとの**兄弟**にも「深い側」を渡す
        -- （表の第 `v-1` 項の第 5 項に `base` を書く）。
        let LS :=
          if (e1 == base + 1) && decide (1 ≤ v) then
            let eo := Lat L (v - 1)
            padL L (v - 1) ++ [(eo.1, eo.2.1, eo.2.2.1, eo.2.2.2.1, base)] ++ L.drop v
          else L
        let rA := conv3 A (dd2 + 1) LA FA (v, s2) (e1, e2) true f0 st1
                    (match B with | q :: _ => some q | [] => nx) (off + 1)
        let rB := conv3 B d LS FA (v, s2) (e1, e2) false false rA.2 nx (off + 1 + A.length)
        (cols ++ rA.1 ++ rB.1, rB.2)
  termination_by 2 * M.length
  decreasing_by
    all_goals
      simp only [List.length_cons, List.length_take, List.length_drop, List.length_tail]
      have h1 : (r.takeWhile (fun q : ℕ × ℕ × ℕ => decide (p.1 < q.1))).length ≤ r.length :=
        (List.takeWhile_sublist _).length_le
      have h2 : (r.dropWhile (fun q : ℕ × ℕ × ℕ => decide (p.1 < q.1))).length ≤ r.length :=
        List.length_dropWhile_le _ r
      omega

/-- 縮約の残余を「もとの深さを保った森」として読む（`rows3.py` の `conv_resid`）。 -/
def convResid (rest : TrioSeq) (rd : ℕ) (Lr : List Lent) (ps pw : ℕ × ℕ)
    (st : St) (nx : Option Col) (off : ℕ) : TrioSeq × St :=
  match rest with
  | [] => ([], st)
  | c :: rs =>
      let i := 1 + deepGe c.1 rs
      let head := (c :: rs).take i
      let tail := (c :: rs).drop i
      let rh := conv3 head rd Lr (List.replicate 12 false) ps pw false false st
                  (match tail with | t :: _ => some t | [] => nx) off
      if tail.isEmpty then rh
      else
        let rt := convResid tail (rd - (c.1 - (tail.headD (0,0,0)).1)) Lr ps pw rh.2 nx (off + i)
        (rh.1 ++ rt.1, rt.2)
  termination_by 2 * rest.length + 1
  decreasing_by
    all_goals
      simp only [List.length_cons, List.length_take, List.length_drop]
      omega

end

/-- 変換の入口（Python の `b2d3`）。 -/
def b2d3 (M : TrioSeq) : TrioSeq :=
  (conv3 M 0 [] [] (0, 0) (0, 0) true false ⟨[], 2, [], M, 0⟩ none 0).1


/-! ### Python (`rows3.b2d3`) との突き合わせ。まず <=5 列から。 -/

#guard Conv3.b2d3 [(0,0,0)] = [(0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,0)] = [(0,0,0), (1,0,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,0), (2,1,0), (3,0,0), (1,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,1,0), (4,0,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (2,1,1), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (4,2,1), (4,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,2,1), (3,2,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,3,1), (5,3,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,0), (1,1,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,2,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,3,0), (5,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (3,0,0), (4,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,0,0), (6,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (3,1,1), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,2,1), (5,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (2,1,0), (1,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (0,0,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (0,0,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (3,1,0), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,1,0), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,2,0), (1,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,3,0), (3,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,1,1), (3,2,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,2,1), (5,3,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (0,0,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (0,0,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,0), (2,2,0), (1,1,0), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,0), (2,1,0), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (0,0,0), (1,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (0,0,0), (1,0,0), (2,1,0), (3,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,0), (2,1,0), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,1,0), (3,1,0), (3,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,0), (2,0,0), (1,0,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,0,0), (1,0,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,1,1), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,2,1), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (0,0,0), (1,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (0,0,0), (1,0,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,2,1), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,3,1), (4,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,1,1), (3,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,2,1), (5,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (0,0,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (0,0,0), (1,0,0)]


/-! **縮約が発火する** <=5 列の 5 個ぜんぶ、6 列の抜き取り、7 列の抜き取り。 -/

#guard Conv3.b2d3 [(0,0,0), (1,1,0), (1,0,0), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,0,0), (2,1,1), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,0), (2,2,1), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,0), (2,2,1), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,0), (2,2,1), (2,2,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,0), (2,2,1), (2,2,0), (3,3,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,0), (4,3,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,0), (2,2,1), (2,0,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,0,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,0), (2,2,1), (2,2,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,0), (4,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,0), (2,2,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,1,0), (3,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,0), (2,2,1), (2,2,0), (1,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,0), (1,0,0), (2,1,0), (2,0,0), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (2,0,0), (3,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,2,1), (2,1,1), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,3,1), (4,2,1), (5,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,2,0), (3,1,1), (4,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,3,0), (5,2,1), (6,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (3,1,0), (4,1,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (5,1,0), (6,1,0), (5,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,1,1), (2,1,0), (3,2,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (3,2,1), (4,2,0), (5,3,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (3,1,1), (3,1,0), (1,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (5,1,0), (6,2,1), (5,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,2,1), (2,0,0), (1,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,3,1), (4,0,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,1,1), (4,1,0), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,2,1), (6,2,0), (5,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,1,0), (2,2,1), (2,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,2,0), (4,3,1), (4,2,1)]

/-! 7 列の抜き取り。 -/

#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,3,0), (4,3,0), (2,1,1), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,0), (6,4,0), (4,2,1), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,3,0), (4,4,1), (5,5,0), (3,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,0), (6,5,1), (7,6,0), (5,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,3,0), (4,2,1), (5,3,0), (1,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,0), (6,3,1), (7,4,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,3,1), (4,3,1), (4,1,0), (5,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,1), (6,4,1), (6,2,0), (7,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,1,0), (2,2,0), (1,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,2,0), (4,3,0), (2,1,0), (3,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,0,0), (4,1,0), (2,1,1), (1,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,0,0), (6,1,0), (4,2,1), (3,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,3,1), (4,4,0), (3,2,1), (4,3,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,1), (6,5,0), (5,3,1), (6,4,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,3,1), (3,1,1), (4,0,0), (2,2,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,1), (5,2,1), (6,0,0), (4,3,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,0,0), (4,1,1), (4,1,0), (5,2,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,0,0), (6,1,0), (7,2,1), (7,2,0), (8,3,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,1,0), (3,0,0), (1,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,2,0), (5,0,0), (2,1,0), (3,0,0)]

end Conv3


/-! ## 9. 対角の像 `ConvDiagT3`

対角 `diagSeqT 0 v = (0,0,0)(1,1,1)(2,2,1)…(v,v,1)` は

* 兄弟がまったく無い（どの列も直前の列の引数）ので `B = []`、
* `is_branch` の分岐列 `(a,1,0)` が 1 本も無いので状態 `prev` を読まない、
* 兄弟が無いので縮約（`contrFind`）も発火しない（`contrFind_nil`）

一番素直な入力である。先頭 2 列 `(0,0,0)(1,1,1)` だけが特別（ここで行 0 と
行 1 の梯子が同時に立って 1 列が 3 列になる）で、3 列目から先は
「1 列が 1 列」の規則正しい尾になる。 -/

namespace Conv3

/-- 対角の尾: `(a,a,1)(a+1,a+1,1)…` を `m` 本。 -/
def Dt (a m : ℕ) : TrioSeq := (List.range' a m).map (fun i => (i, i, 1))

/-- その像: `(a,a-1,1)(a+1,a,1)…` を `m` 本。 -/
def Ot (a m : ℕ) : TrioSeq := (List.range' a m).map (fun i => (i, i - 1, 1))

@[simp] theorem Dt_zero (a : ℕ) : Dt a 0 = [] := rfl
@[simp] theorem Ot_zero (a : ℕ) : Ot a 0 = [] := rfl

theorem Dt_succ (a m : ℕ) : Dt a (m + 1) = (a, a, 1) :: Dt (a + 1) m := by
  simp [Dt, List.range'_succ]

theorem Ot_succ (a m : ℕ) : Ot a (m + 1) = (a, a - 1, 1) :: Ot (a + 1) m := by
  simp [Ot, List.range'_succ]

/-- 尾の第 `k+2` 列を読む直前の祖先の鎖。長さは `k+4`。 -/
def STd : ℕ → List (ℕ × ℕ)
  | 0 => [(0, 0), (0, 0), (1, 0), (2, 1)]
  | (k + 1) => STd k ++ [(k + 3, 1)]

/-- 尾の第 `k+2` 列を読む直前の段の表。長さは `k+2`。 -/
def Ld : ℕ → List Lent
  | 0 => [(1, 0, false, 0, 1), (2, 1, false, 2, 2)]
  | (k + 1) => Ld k ++ [(k + 3, 1, true, k + 3, k + 3)]

theorem STd_len (k : ℕ) : (STd k).length = k + 4 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [STd, ih]

theorem Ld_len (k : ℕ) : (Ld k).length = k + 2 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Ld, ih]

/-- 対角の表は最初から「潰した形」（第 5 項 = 第 1 項）なので、`LA` を作る
ときの `lentTrunc` は何もしない。 -/
theorem Ld_trunc (k : ℕ) : (Ld k).map lentTrunc = Ld k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Ld, ih, lentTrunc]

theorem STd_take (k : ℕ) : (STd k).take (k + 4) = STd k := by
  have h := STd_len k
  exact List.take_of_length_le (by omega)

theorem Ld_take (k : ℕ) : (Ld k).take (k + 2) = Ld k := by
  have h := Ld_len k
  exact List.take_of_length_le (by omega)

theorem STd_rev (k : ℕ) : ∃ R, (STd k).reverse = (k + 2, 1) :: R := by
  cases k with
  | zero => exact ⟨[(1, 0), (0, 0), (0, 0)], rfl⟩
  | succ k => exact ⟨(STd k).reverse, by simp [STd]⟩


theorem okPlace_STd (k : ℕ) : okPlace (STd k) (k + 4) (k + 3) = true := by
  obtain ⟨R, hR⟩ := STd_rev k
  unfold okPlace
  rw [if_neg (by omega), if_neg (by omega), STd_take, hR]
  simp

theorem fit_STd (k : ℕ) : fit (STd k) (k + 4) (k + 3) = some (k + 4) := by
  have hl : (STd k).length + 1 - (k + 4) = 1 := by rw [STd_len]; omega
  unfold fit
  rw [hl]
  simp only [fitAux]
  rw [if_pos (okPlace_STd k)]

/-- `Ld k` の最終項の Bool（`k = 0` だけ `false`）。実際には使われない
（`lad1` の第 2 条項 `s2 = pl2 + 1` が先に落ちるので `force1` は読まれない）。 -/
def bLd (k : ℕ) : Bool := decide (k ≠ 0)

theorem Lat_Ld (k : ℕ) : Lat (Ld k) (k + 1) = (k + 2, 1, bLd k, k + 2, k + 2) := by
  cases k with
  | zero => decide
  | succ k =>
      have hlen : (Ld k).length = k + 2 := Ld_len k
      have h : ((Ld k) ++ [((k + 3 : ℕ), (1 : ℕ), true, (k + 3 : ℕ), (k + 3 : ℕ))])[k + 2]?
          = some (k + 3, 1, true, k + 3, k + 3) := by
        have := List.getElem?_concat_length (l := Ld k)
          (a := ((k + 3 : ℕ), (1 : ℕ), true, (k + 3 : ℕ), (k + 3 : ℕ)))
        rwa [hlen] at this
      show Lat (Ld k ++ [((k + 3 : ℕ), (1 : ℕ), true, (k + 3 : ℕ), (k + 3 : ℕ))]) (k + 2) = _
      unfold Lat
      rw [h]
      simp [bLd]

theorem padL_Ld (k : ℕ) : padL (Ld k) (k + 2) = Ld k := by
  unfold padL
  rw [if_neg (by rw [Ld_len]; omega), Ld_take]

theorem getD_rep (n : ℕ) : (List.replicate n false).getD n true = true := by
  simp [List.getD]

theorem take_rep (n : ℕ) :
    (List.replicate n false).take n ++ [false] = List.replicate (n + 1) false := by
  rw [List.take_of_length_le (by simp)]
  simp [List.replicate_succ']

theorem rep_app (n : ℕ) :
    List.replicate n false ++ [false] = List.replicate (n + 1) false := by
  simp [List.replicate_succ']


theorem Dt_takeWhile : ∀ (m a b : ℕ), a < b →
    (Dt b m).takeWhile (fun q : ℕ × ℕ × ℕ => decide (a < q.1)) = Dt b m := by
  intro m
  induction m with
  | zero => intro a b _; rfl
  | succ m ih =>
      intro a b hab
      rw [Dt_succ, List.takeWhile_cons_of_pos (by simpa using hab), ih a (b + 1) (by omega)]

theorem Dt_dropWhile : ∀ (m a b : ℕ), a < b →
    (Dt b m).dropWhile (fun q : ℕ × ℕ × ℕ => decide (a < q.1)) = [] := by
  intro m
  induction m with
  | zero => intro a b _; rfl
  | succ m ih =>
      intro a b hab
      rw [Dt_succ, List.dropWhile_cons_of_pos (by simpa using hab), ih a (b + 1) (by omega)]


@[simp] theorem conv3_nil (d : ℕ) (L : List Lent) (F : List Bool) (ps pw : ℕ × ℕ)
    (first force : Bool) (st : St) (nx : Option Col) (off : ℕ) :
    conv3 [] d L F ps pw first force st nx off = ([], st) := by
  rw [conv3.eq_def]

theorem STd_succ (k : ℕ) : STd (k + 1) = STd k ++ [(k + 3, 1)] := rfl

theorem Ld_succ (k : ℕ) : Ld (k + 1) = Ld k ++ [(k + 3, 1, true, k + 3, k + 3)] := rfl

set_option maxHeartbeats 1000000 in
/-- 尾の 1 歩: 第 `k+2` 列 `(k+2,k+2,1)` は像の 1 列 `(k+4,k+3,1)` になり、
状態の祖先の鎖は `STd k -> STd (k+1)` に伸びる。行 0 の梯子 `lad0` は
`d = k+4 > h1 = k+3` で落ち、行 1 の梯子 `lad1` は `s2 = 1 != pl2+1 = 2` で落ちる。 -/
theorem conv3_tail_step (m k : ℕ) (st : St) (nx : Option Col) (off : ℕ)
    (h : st.ST = STd k) :
    conv3 (Dt (k + 2) (m + 1)) (k + 4) (Ld k) (List.replicate (k + 2) false)
      (k + 1, 1) (k + 2, 1) true false st nx off
    = ((k + 4, k + 3, 1) ::
        (conv3 (Dt (k + 3) m) (k + 5) (Ld (k + 1)) (List.replicate (k + 3) false)
          (k + 2, 1) (k + 3, 1) true false
          ⟨STd (k + 1), st.prev, st.dmap.take (k + 2) ++ [k + 4], st.Mo, st.nc⟩
          nx (off + 1)).1,
       (conv3 (Dt (k + 3) m) (k + 5) (Ld (k + 1)) (List.replicate (k + 3) false)
          (k + 2, 1) (k + 3, 1) true false
          ⟨STd (k + 1), st.prev, st.dmap.take (k + 2) ++ [k + 4], st.Mo, st.nc⟩
          nx (off + 1)).2) := by
  have hk1 : k + 2 - 1 = k + 1 := by omega
  have hk0 : ¬(k + 2 = 0) := by omega
  have h3 : k + 2 + 1 = k + 3 := by omega
  have h5 : k + 4 + 1 = k + 5 := by omega
  have hbeq : ((k + 1 : ℕ) == k) = false := by simp
  have hib : isBranch ((k : ℕ) + 2, (k : ℕ) + 2, (1 : ℕ)) = false := by simp [isBranch]
  rw [Dt_succ, conv3.eq_def]
  simp only [hk1, if_neg hk0, hib, Lat_Ld, Bool.false_eq_true, if_false,
    Dt_takeWhile m (k + 2) (k + 3) (by omega), Dt_dropWhile m (k + 2) (k + 3) (by omega),
    h]
  simp [padL_Ld, Ld_trunc, rep_app, STd_take, fit_STd, okPlace_STd, STd_len, STd_succ,
    Ld_succ, hbeq, h3, h5]


/-- 尾ぜんぶ: `(k+2,k+2,1)…` を `m` 本読むと像は `(k+4,k+3,1)…` の `m` 本。 -/
theorem conv3_tail (m : ℕ) : ∀ (k : ℕ) (st : St) (nx : Option Col) (off : ℕ),
    st.ST = STd k →
    (conv3 (Dt (k + 2) m) (k + 4) (Ld k) (List.replicate (k + 2) false)
      (k + 1, 1) (k + 2, 1) true false st nx off).1 = Ot (k + 4) m := by
  induction m with
  | zero => intro k st nx off _; simp
  | succ m ih =>
      intro k st nx off h
      rw [conv3_tail_step m k st nx off h]
      have e1 : k + 1 + 4 = k + 5 := by omega
      have e2 : k + 1 + 2 = k + 3 := by omega
      have e3 : k + 1 + 1 = k + 2 := by omega
      have := ih (k + 1) ⟨STd (k + 1), st.prev, st.dmap.take (k + 2) ++ [k + 4], st.Mo, st.nc⟩
        nx (off + 1) rfl
      simp only [e1, e2, e3] at this
      rw [this, Ot_succ]
      simp

/-- 先頭の列 `(0,0,0)`。梯子は 2 つとも落ち、像は `(0,0,0)` 1 列。 -/
theorem conv3_lvl0 (v : ℕ) (st : St) (nx : Option Col) (off : ℕ) (h : st.ST = []) :
    (conv3 ((0, 0, 0) :: Dt 1 v) 0 [] [] (0, 0) (0, 0) true false st nx off).1
    = (0, 0, 0) :: (conv3 (Dt 1 v) 1 [(0, 0, true, 0, 0)] [false] (0, 0) (0, 0) true true
        ⟨[(0, 0)], st.prev, st.dmap.take 0 ++ [0], st.Mo, st.nc⟩ nx (off + 1)).1 := by
  rw [conv3.eq_def]
  simp [Dt_takeWhile v 0 1 (by omega), Dt_dropWhile v 0 1 (by omega), h,
    okPlace, fit, fitAux, padL]

/-- 2 列目 `(1,1,1)`。行 0 と行 1 の梯子が同時に立ち、1 列が 3 列になる。
ここで祖先の鎖が `STd 0 = (0,0)(0,0)(1,0)(2,1)`、段の表が `Ld 0` になる。 -/
theorem conv3_lvl1 (m : ℕ) (st : St) (nx : Option Col) (off : ℕ) (h : st.ST = [(0, 0)]) :
    (conv3 (Dt 1 (m + 1)) 1 [(0, 0, true, 0, 0)] [false] (0, 0) (0, 0) true true st nx off).1
    = (1, 0, 0) :: (2, 1, 0) :: (3, 2, 1) ::
      (conv3 (Dt 2 m) 4 (Ld 0) (List.replicate 2 false) (1, 1) (2, 1) true false
        ⟨STd 0, st.prev, st.dmap.take 1 ++ [3], st.Mo, st.nc⟩ nx (off + 1)).1 := by
  rw [Dt_succ, conv3.eq_def]
  simp [Dt_takeWhile m 1 2 (by omega), Dt_dropWhile m 1 2 (by omega), h,
    okPlace, Lat, padL, STd, Ld, isBranch, contrFind_nil, lentTrunc]


theorem conv3_tail0 (m : ℕ) (st : St) (nx : Option Col) (off : ℕ) (h : st.ST = STd 0) :
    (conv3 (Dt 2 m) 4 (Ld 0) (List.replicate 2 false) (1, 1) (2, 1) true false st nx off).1
      = Ot 4 m := by
  simpa using conv3_tail m 0 st nx off h

theorem mapDiag : ∀ (n a : ℕ), 1 ≤ a →
    (List.range' a n).map (fun j : ℕ => (j, j, min j 1)) = Dt a n := by
  intro n
  induction n with
  | zero => intro a _; rfl
  | succ n ih =>
      intro a ha
      rw [List.range'_succ, List.map_cons, ih (a + 1) (by omega), Dt_succ]
      simp [Nat.min_eq_right ha]

theorem mapDD : ∀ (n a : ℕ), 3 ≤ a → (List.range' a n).map ddcolT = Ot a n := by
  intro n
  induction n with
  | zero => intro a _; rfl
  | succ n ih =>
      intro a ha
      rw [List.range'_succ, List.map_cons, ih (a + 1) (by omega), Ot_succ]
      simp [ddcolT, Nat.min_eq_right (show 1 ≤ a - 2 by omega)]

theorem diagSeqT_cons (v : ℕ) : diagSeqT 0 v = (0, 0, 0) :: Dt 1 v := by
  simp [diagSeqT, List.range'_succ, mapDiag v 1 (le_refl 1)]

theorem ddiagSeqT_split (n : ℕ) :
    ddiagSeqT (n + 3) = (0, 0, 0) :: (1, 0, 0) :: (2, 1, 0) :: (3, 2, 1) :: Ot 4 n := by
  simp [ddiagSeqT, List.range_eq_range', List.range'_succ, ddcolT,
    mapDD n 4 (by omega)]

/-- **対角の像**（`ConvDiagT3` の本体）。 -/
theorem b2d3_diagSeqT (v : ℕ) :
    b2d3 (diagSeqT 0 v) = if v = 0 then ddiagSeqT 0 else ddiagSeqT (v + 2) := by
  unfold b2d3
  rw [diagSeqT_cons, conv3_lvl0 v _ none 0 rfl]
  cases v with
  | zero => simp [ddiagSeqT, ddcolT]
  | succ n =>
      rw [if_neg (by omega), conv3_lvl1 n _ none 1 rfl, conv3_tail0 n _ none 2 rfl,
        show n + 1 + 2 = n + 3 from by omega, ddiagSeqT_split n]

end Conv3

/-! ## 10. `ConvDiagT3` は Lean の `Conv3.b2d3` について証明ずみ -/

/-- **`ConvDiagT3` の証明**。`Dbms3.lean` が変換器に課していた 2 命題のうち、
対角の側はこれで閉じた。 -/
theorem ConvDiagT3_b2d3 : ConvDiagT3 Conv3.b2d3 := Conv3.b2d3_diagSeqT

/-- 残るのは `ReindexT1` ただ 1 つ、という形にまとめたもの。

`Conv3.b2d3` は Python の `rows3.b2d3`（縮約つき v11）の写経なので、
`ReindexT1 Conv3.b2d3` は Python 側で測っている性質そのものである。
いまの v11 はこれをまだ満たしていない（`tools/dbms/NOTES.md` の
「ImgClosedT の測定」: <=5 列で 28 個の反例が確定）。 -/
theorem ST_D3_b2d3 (h2 : Wset.TowerGraft2) (he : Wset.TowerExp)
    (H : ReindexT1 Conv3.b2d3) {M : TrioSeq} (hM : ST_TS M) : ST_D3 (Conv3.b2d3 M) :=
  ST_D3_conv3_holds h2 he H ConvDiagT3_b2d3 hM

/-! 対角の像を実際に計算して確かめる（`tools/dbms/rows3.py` の `b2d3` と一致）。 -/
#guard Conv3.b2d3 (diagSeqT 0 0) = ddiagSeqT 0
#guard Conv3.b2d3 (diagSeqT 0 1) = ddiagSeqT 3
#guard Conv3.b2d3 (diagSeqT 0 2) = ddiagSeqT 4
#guard Conv3.b2d3 (diagSeqT 0 5) = ddiagSeqT 7
#guard Conv3.b2d3 (diagSeqT 0 9) = ddiagSeqT 11


/-! ## 11. `ReindexT1` の分解（課題 F4）

`ReindexT1` は「像が展開で閉じている」＋「順序が保たれる」＋「挟み撃ち」の
3 つに割れる。**3 つとも `conv3` だけの構文的命題**（順序数も読み `read3` も
出てこない）ので、そのまま Python で全数採点できる。

    ImgClosedT3 : 任意の A, m>=1 に ある BMS 標準形 B で (conv3 A)<m> = conv3 B
    OrderT3     : translate M <o translate N  <->  seqlex (conv3 M) (conv3 N)
    SandwichT3  : conv3 (A<n>) <=seqlex (conv3 A)<n+1>   （上, C2@1）
                  (conv3 A)<n> <=seqlex conv3 (A<n+1>)   （下, C1@1）

`ReindexT1` が要求する `B` の位置 `A<n> ≤o B <o A` は、この挟み撃ちの
上下 2 本からちょうど出る（`ReindexT1_of_sandwich`）。

`SandwichL` が担っているのは「`conv3 B = (conv3 A)⟦n+1⟧` が `conv3 A` より
真に小さい」ことだけである。それは像が `blockok 0`（行 0 が 0 から始まり隣接
段差 1 以下）で 2 列以上なら **`seqlex_oper` で証明できる**ので、`SandwichL`
そのものを仮定しない版 `ReindexT1_of_block` が取れる。そちらで Python が
保証すべきものは

    ImgClosedT3 ＋ OrderT3 ＋ SandwichU ＋ 像の衛生（blockok と長さ）

だけになる。**`SandwichL` 自体は像の衛生からは出ない**（`seqlex_oper` が言うのは
`(conv3 A)⟦n⟧ <seqlex conv3 A` であって、右辺が `conv3 (A⟦n+1⟧)` の版ではない）。
`conv3` v12 は `SandwichL` を <=6 列 41930 対のうち 352 対（<=7 列 386405 対の
うち 4696 対）で破っているので、実用上も `ReindexT1_of_block` の側を採るべきで
ある。`SandwichU` のほうは <=6 列で破れ 0（<=7 列で 8）。 -/

/-- 列辞書式の「以下」。 -/
def sle3 (M N : TrioSeq) : Prop := M = N ∨ seqlex M N

theorem seqlex_irrefl (M : TrioSeq) : ¬ seqlex M M := by
  induction M with
  | nil => simp
  | cons p M ih =>
    rw [seqlex_cons_cons]
    rintro (h | ⟨-, h⟩)
    · exact absurd h (by simp [collt])
    · exact ih h

theorem ne_of_seqlex {M N : TrioSeq} (h : seqlex M N) : M ≠ N := by
  rintro rfl
  exact seqlex_irrefl _ h

/-- **DBMS 側の展開は列辞書式を下げる。** 標準形性はいらない（`blockok` だけ）。
`m_step_decreases`（`Decrease.lean:578`）と `olt_iff_seqlex`（`Seqlex.lean:408`）の
組み合わせ。これが `SandwichL` の中身である。 -/
theorem seqlex_oper {C : TrioSeq} {m : ℕ} (hb : blockok 0 C) (hL : 1 < C.length)
    (hm : 1 ≤ m) : seqlex (C⟦m⟧) C := by
  have h1 : translate (C⟦m⟧) <o translate C := m_step_decreases hL hm
  have hne : C⟦m⟧ ≠ C := by
    intro h
    rw [h] at h1
    exact olt_irrefl _ h1
  exact (olt_iff_seqlex (blockok_oper hb hm) hb hne).1 h1

/-! ### 11.1 3 つの命題 -/

/-- **像は展開で閉じている**。`tools/dbms/imgfast.py` が測っている命題そのもの。
いまの `conv3` v12 では <=5 列で 26 個・<=6 列で 294 個の A が反例
（`python3 imgfast.py fast 5 / fast 6`）。

下の分解が実際に使うのは `m = n + 1`、つまり **`m ≥ 2` だけ**である。ただし実測
（<=5 列 x m<=3 の 3051 対）では破れは m=2 が 25 対・m=3 が 26 対で **m=1 の破れは
0 件**なので、`1 ≤ m` を `2 ≤ m` に弱めても反例は 1 件も減らない。 -/
def ImgClosedT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {A : TrioSeq}, ST_TS A → 1 < A.length → ∀ m : ℕ, 1 ≤ m →
    ∃ B : TrioSeq, ST_TS B ∧ (conv3 A)⟦m⟧ = conv3 B

/-- **順序保存**。2 行の `conC_olt_iff_seqlex`（`Dbms.lean:2791`）の 3 行版だが、
右辺が **DBMS 側の** 列辞書式であるところが違う（2 行版は BMS 側の `seqlex M N`
で止めてある）。標準形の上では `translate` が `seqlex` への順序同型
（`olt_ST_iff_seqlex`）なので、これは「`conv3` が列辞書式の順序埋め込み」と同値:

    seqlex M N  <->  seqlex (conv3 M) (conv3 N)

この形なら順序数を一切通さずに Python で採点できる（`OrderT3_iff_seqemb`）。
**実測: `conv3` v12 は <=6 列 8387 個・<=7 列 77282 個で、辞書式に並べ替えても
像の辞書式で並べ替えても順序が完全に同一（位置ずれ 0、像の重複も 0）。** -/
def OrderT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {M N : TrioSeq}, ST_TS M → ST_TS N →
    (translate M <o translate N ↔ seqlex (conv3 M) (conv3 N))

/-- **挟み撃ちの上**（`m_cofinal.py` の C2@1）。シートの正解 f では 38880 対で
反例 0。`conv3` v12 の実測は <=6 列 41930 対で破れ 0 / <=7 列 386405 対で破れ 8
（n = 1..5）。その 8 対は **A が 2 個だけ**（n = 2..5 の 4 本ずつ）:

    (0,0,0)(1,1,1)(2,1,0)(3,2,1)(3,2,0)(3,1,0)(1,1,1)
    (0,0,0)(1,1,1)(2,2,1)(3,2,1)(3,2,0)(3,1,0)(1,1,1)

これは `tools/dbms/rows3.py` の残る欠陥 (c)「残余ありの縮約」の 2 個と同じ行列で、
食い違いは第 8 列の行 1 が 2 か 1 か（`f(A⟦n⟧)` が `(5,2,0)`、`(f A)⟦n+1⟧` が
`(5,1,0)`）。ImgClosedT の破れと同じ「末尾の行 1 が 1 だけずれる」病である。 -/
def SandwichUT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {A : TrioSeq}, ST_TS A → 1 < A.length → ∀ n : ℕ, 1 ≤ n →
    sle3 (conv3 (A⟦n⟧)) ((conv3 A)⟦n + 1⟧)

/-- **挟み撃ちの下**（`m_cofinal.py` の C1@1）。シートの正解 f では 38880 対で
反例 0 だが、`conv3` v12 の実測は <=6 列 41930 対で破れ 352 / <=7 列 386405 対で
破れ 4696（n = 1..5）。**下の `ReindexT1_of_block` はこれを使わない。** -/
def SandwichLT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {A : TrioSeq}, ST_TS A → 1 < A.length → ∀ n : ℕ, 1 ≤ n →
    sle3 ((conv3 A)⟦n⟧) (conv3 (A⟦n + 1⟧))

/-- 挟み撃ち（上下）。 -/
def SandwichT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  SandwichUT3 conv3 ∧ SandwichLT3 conv3

/-- 像が `blockok 0`（行 0 が 0 から始まり、隣接する段差が 1 以下）。
実測: `conv3` v12 は <=7 列 77282 個で破れ 0。 -/
def ImgBlockT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {A : TrioSeq}, ST_TS A → blockok 0 (conv3 A)

/-- 像の長さ（`|A| > 1` なら像も 2 列以上）。
実測: `conv3` v12 は <=7 列 77282 個で破れ 0。 -/
def ImgLenT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {A : TrioSeq}, ST_TS A → 1 < A.length → 1 < (conv3 A).length

/-! ### 11.2 `OrderT3` から出る道具 -/

/-- `conv3` の像で `≤` なら、もとの項も `≤o`。`conv3 M = conv3 N` の枝は
`OrderT3` から出る単射性で潰す。 -/
theorem ole_of_sle3 {conv3 : TrioSeq → TrioSeq} (hO : OrderT3 conv3)
    {M N : TrioSeq} (hM : ST_TS M) (hN : ST_TS N)
    (h : sle3 (conv3 M) (conv3 N)) : translate M ≤o translate N := by
  rcases h with heq | hlt
  · rcases seqlex_total M N with rfl | hs | hs
    · exact ole_refl _
    · exact Or.inl ((olt_ST_iff_seqlex hM hN (ne_of_seqlex hs)).2 hs)
    · have h1 : translate N <o translate M :=
        (olt_ST_iff_seqlex hN hM (ne_of_seqlex hs)).2 hs
      have h2 : seqlex (conv3 N) (conv3 M) := (hO hN hM).1 h1
      rw [heq] at h2
      exact absurd h2 (seqlex_irrefl _)
  · exact Or.inl ((hO hM hN).2 hlt)

/-- `OrderT3` は単射性を含む。 -/
theorem conv3_injective {conv3 : TrioSeq → TrioSeq} (hO : OrderT3 conv3)
    {M N : TrioSeq} (hM : ST_TS M) (hN : ST_TS N) (h : conv3 M = conv3 N) : M = N := by
  rcases seqlex_total M N with rfl | hs | hs
  · rfl
  · have h2 : seqlex (conv3 M) (conv3 N) :=
      (hO hM hN).1 ((olt_ST_iff_seqlex hM hN (ne_of_seqlex hs)).2 hs)
    rw [h] at h2
    exact absurd h2 (seqlex_irrefl _)
  · have h2 : seqlex (conv3 N) (conv3 M) :=
      (hO hN hM).1 ((olt_ST_iff_seqlex hN hM (ne_of_seqlex hs)).2 hs)
    rw [h] at h2
    exact absurd h2 (seqlex_irrefl _)

/-! ### 11.3 主定理: `ReindexT1` の分解 -/

/-- **`ReindexT1` は `ImgClosedT3` ＋ `OrderT3` ＋ `SandwichT3` から出る。**

`m := n + 1` を取り、`ImgClosedT3` が返す `B`（`(conv3 A)⟦n+1⟧ = conv3 B`）を使う。

* 上: `SandwichU` の `n` 版が `conv3 (A⟦n⟧) ≤ conv3 B` を与え、`OrderT3` で
  `translate (A⟦n⟧) ≤o translate B` になる。
* 下: `SandwichL` の `n+1` 版が `conv3 B ≤ conv3 (A⟦n+2⟧)` を与え、`OrderT3` で
  `translate B ≤o translate (A⟦n+2⟧)`。あとは `m_step_decreases` で
  `translate (A⟦n+2⟧) <o translate A`。

これが「Sandwich から `B` の位置 `A⟦n⟧ ≤o B <o A` が出る」の中身である。 -/
theorem ReindexT1_of_sandwich {conv3 : TrioSeq → TrioSeq}
    (hI : ImgClosedT3 conv3) (hO : OrderT3 conv3) (hS : SandwichT3 conv3) :
    ReindexT1 conv3 := by
  obtain ⟨hU, hL⟩ := hS
  intro A hA hlen n hn
  obtain ⟨B, hB, heq⟩ := hI hA hlen (n + 1) (by omega)
  refine ⟨n + 1, B, by omega, hB, ?_, ?_, heq⟩
  · have h := hU hA hlen n hn
    rw [heq] at h
    exact ole_of_sle3 hO (ST_TS.oper hA hn) hB h
  · have h := hL hA hlen (n + 1) (by omega)
    rw [heq] at h
    have h1 : translate B ≤o translate (A⟦n + 1 + 1⟧) :=
      ole_of_sle3 hO hB (ST_TS.oper hA (by omega : 1 ≤ n + 1 + 1)) h
    exact ole_olt_trans h1 (m_step_decreases hlen (by omega : 1 ≤ n + 1 + 1))

/-- **下側の挟み撃ちは像の衛生から証明できる**（`SandwichL` を仮定しない版）。

`SandwichL` の役目は「`conv3 B = (conv3 A)⟦n+1⟧` が `conv3 A` より真に小さい」
ことを言うだけなので、像が `blockok 0` で 2 列以上なら `seqlex_oper` で出る。
Python が保証すべきものは

    ImgClosedT3 ＋ OrderT3 ＋ SandwichU ＋ ImgBlockT3 ＋ ImgLenT3

だけになる。うしろ 2 つは変換器の出力の形の話（行 0 が 0 から始まって 1 段ずつ）で
中身が無い。 -/
theorem ReindexT1_of_block {conv3 : TrioSeq → TrioSeq}
    (hI : ImgClosedT3 conv3) (hO : OrderT3 conv3) (hU : SandwichUT3 conv3)
    (hb : ImgBlockT3 conv3) (hlen2 : ImgLenT3 conv3) :
    ReindexT1 conv3 := by
  intro A hA hlen n hn
  obtain ⟨B, hB, heq⟩ := hI hA hlen (n + 1) (by omega)
  refine ⟨n + 1, B, by omega, hB, ?_, ?_, heq⟩
  · have h := hU hA hlen n hn
    rw [heq] at h
    exact ole_of_sle3 hO (ST_TS.oper hA hn) hB h
  · refine (hO hB hA).2 ?_
    rw [← heq]
    exact seqlex_oper (hb hA) (hlen2 hA hlen) (by omega)

/-- `ST_D3_conv3` を分解した形でまとめ直したもの。 -/
theorem ST_D3_conv3_of_parts (h2 : Wset.TowerGraft2) (he : Wset.TowerExp)
    {conv3 : TrioSeq → TrioSeq}
    (hI : ImgClosedT3 conv3) (hO : OrderT3 conv3) (hU : SandwichUT3 conv3)
    (hb : ImgBlockT3 conv3) (hlen2 : ImgLenT3 conv3) (hd : ConvDiagT3 conv3)
    {M : TrioSeq} (hM : ST_TS M) : ST_D3 (conv3 M) :=
  ST_D3_conv3_holds h2 he (ReindexT1_of_block hI hO hU hb hlen2) hd hM

/-! ## 12. `OrderT3` を証明するには何が要るか

2 行側の `conC_olt_iff_seqlex`（`Dbms.lean:2791`）は 2 行だけである:

    rw [readC_conC_ST hM, readC_conC_ST hN]
    exact olt_iff_seqlex (blockok_ST_PS hM) (blockok_ST_PS hN) hne

つまり中身は 2 つで、**どちらも 3 行にはまだ無い**。

1. **読みの保存** `readCon (conC M) = translate M`（`Dbms.lean:2765`）。
   `readC_convC` の証明は `Dbms.lean` の §5-§8、2600 行ぶんある。
   3 行では読み `read3` そのものがまだ書かれていない（`readD` は
   「ブロックの先頭で段が親と同じ・次が `p + (1,1)` なら影として捨てる」という
   節を `translate` に 1 つ足したもの。3 行では行 1 の影と行 2 の影の 2 種類が
   あるので節は 2 つ要る）。

2. **DBMS 側の順序同型**。2 行版はここで `olt_iff_seqlex` を **BMS 側の**
   `M`, `N` に当てて逃げている（右辺が `seqlex M N`）。`OrderT3` は右辺が
   `seqlex (conv3 M) (conv3 N)` なので、DBMS 側で

       read3 C <o read3 D  ↔  seqlex C D

   が要る。`read3` は影の列を読み飛ばすので `translate` ではなく、
   `olt_iff_seqlex` をそのまま当てることはできない。`blockok` に当たる
   「影の作法」（影の直後には必ずその昇格列が来る、等）を DBMS 側の不変量
   `dok` として立て、それが `conv3` の像で成り立つことと、`dok` の上で
   `read3` が `seqlex` への順序同型になることを示す必要がある。

下の `OrderT3_of_read` はこの 2 段をそのまま組んだもの（`read3` と `dok` は
関数／述語の変数）。**証明は 3 行**で、仕事は全部 3 つの仮定の側にある。 -/

/-- 読みの保存（2 行の `readC_conC_ST` の 3 行版）。 -/
def ReadT3 (read3 : TrioSeq → Three) (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {M : TrioSeq}, ST_TS M → read3 (conv3 M) = translate M

/-- 像は DBMS 側の作法 `dok` を満たす（2 行の `blockok_ST_PS` に当たる）。 -/
def ImgDokT3 (dok : TrioSeq → Prop) (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {M : TrioSeq}, ST_TS M → dok (conv3 M)

/-- `dok` の上で `read3` は列辞書式への順序同型（2 行の `olt_iff_seqlex` に当たる）。 -/
def ReadLexT3 (read3 : TrioSeq → Three) (dok : TrioSeq → Prop) : Prop :=
  ∀ {C D : TrioSeq}, dok C → dok D → (read3 C <o read3 D ↔ seqlex C D)

/-- **`OrderT3` は「読みの保存」＋「DBMS 側の順序同型」から出る。**

証明は 3 行で、仕事は全部 3 つの仮定の側にある。 -/
theorem OrderT3_of_read {read3 : TrioSeq → Three} {dok : TrioSeq → Prop}
    {conv3 : TrioSeq → TrioSeq}
    (hr : ReadT3 read3 conv3) (hk : ImgDokT3 dok conv3) (hx : ReadLexT3 read3 dok) :
    OrderT3 conv3 := by
  intro M N hM hN
  rw [← hr hM, ← hr hN]
  exact hx (hk hM) (hk hN)

/-! ### 12.1 `OrderT3` の順序数を通らない言い換え

標準形の上では `translate` が `seqlex` への順序同型（`olt_ST_iff_seqlex`）なので、
`OrderT3` は「`conv3` が列辞書式の順序埋め込みである」と**同値**である。
こちらは項も読みも順序数も出てこないので、Python で

    L を辞書式に並べ替えたもの  と  L を像の辞書式で並べ替えたもの  が一致するか

を見るだけで全数採点できる（実測: `conv3` v12 は <=6 列 8387 個・<=7 列 77282 個で
位置ずれ 0、像の重複も 0）。読み `read3` を書かずに `OrderT3` を証明する道があるなら
この形（`conv3` の構造帰納法）だろう。 -/

/-- `conv3` は列辞書式の順序埋め込み。 -/
def SeqEmbT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {M N : TrioSeq}, ST_TS M → ST_TS N → (seqlex M N ↔ seqlex (conv3 M) (conv3 N))

/-- **`OrderT3` と `SeqEmbT3` は同値。** -/
theorem OrderT3_iff_seqemb {conv3 : TrioSeq → TrioSeq} :
    OrderT3 conv3 ↔ SeqEmbT3 conv3 := by
  constructor
  · intro hO M N hM hN
    by_cases h : M = N
    · subst h
      exact iff_of_false (seqlex_irrefl _) (seqlex_irrefl _)
    · exact ((olt_ST_iff_seqlex hM hN h).symm).trans (hO hM hN)
  · intro hE M N hM hN
    by_cases h : M = N
    · subst h
      exact iff_of_false (olt_irrefl _) (seqlex_irrefl _)
    · exact (olt_ST_iff_seqlex hM hN h).trans (hE hM hN)

end TRIO

#print axioms TRIO.not_olt_len_one_T
#print axioms TRIO.diag_cofinal_T
#print axioms TRIO.ST_D3_conv3_diag
#print axioms TRIO.ST_D3_descend
#print axioms TRIO.ST_D3_conv3
#print axioms TRIO.ST_D3_conv3_holds
#print axioms TRIO.Conv3.b2d3_diagSeqT
#print axioms TRIO.ConvDiagT3_b2d3
#print axioms TRIO.ST_D3_b2d3

#print axioms TRIO.seqlex_oper
#print axioms TRIO.ole_of_sle3
#print axioms TRIO.conv3_injective
#print axioms TRIO.ReindexT1_of_sandwich
#print axioms TRIO.ReindexT1_of_block
#print axioms TRIO.ST_D3_conv3_of_parts
#print axioms TRIO.OrderT3_of_read
#print axioms TRIO.OrderT3_iff_seqemb
