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
まだ Lean にないので、**関数変数として抽象化**してある。Python 側が保証すべき
命題はこのファイルの `ReindexT1` と `ConvDiagT3` の 2 つだけになる。
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

end TRIO

#print axioms TRIO.not_olt_len_one_T
#print axioms TRIO.diag_cofinal_T
#print axioms TRIO.ST_D3_conv3_diag
#print axioms TRIO.ST_D3_descend
#print axioms TRIO.ST_D3_conv3
#print axioms TRIO.ST_D3_conv3_holds
