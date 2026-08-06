/-
Wchar.lean: `W a` の**初等的な特徴づけ**。

`Aop` の 3 節のうち、節 3 は長さ 2 以上では節 2 に吸収される
（`aop_clause3_to_clause2`: `domT` の末尾列は親を持たないので
`M⟦n⟧ = Pred M = M.dropLast = graft M []`）。節 3 が本質的に効くのは長さ 1
だけで、そこでは `oper` が恒等なので節 2 は何も与えない。したがって `A1`
（不動点等式）から

```
|S| = 0            →  S ∈ W a
|S| = 1            →  (S ∈ W a  ↔  lev S 0 ≤ a)
|S| ≥ 2            →  (S ∈ W a  ↔  ∀ n ≥ 1, S⟦n⟧ ∈ W a)
```

が**厳密に**成り立つ。`W a` は最小不動点なので、これは

> `W a` = 「どの `n` の選び方でも、BM4 展開が有限回で
>   **レベル ≤ a の長さ 1 以下の列**に到達する」列の集合

という読み方に対応する。段 `a` の役割は「到達してよい根の大きさの上限」だけ。
-/
import Wset

namespace TRIO

open Wset

/-! ## 長さ 1 では `oper` は恒等 -/

theorem oper_of_length_one {S : TrioSeq} (h : S.length = 1) (n : ℕ) :
    S⟦n⟧ = S := by
  simp only [oper]
  rw [if_pos (by omega)]

/-! ## 節 3 は長さ 2 以上で節 2 に吸収される -/

/-- **Clause 3 collapses into clause 2 for length ≥ 2**: a `domT` sequence's
expansion IS its peel, which clause 3 already supplies at `z = []`. -/
theorem aop_clause3_to_clause2 {m : ℕ} {X : Set TrioSeq} {M : TrioSeq}
    (hM2 : 2 ≤ M.length) (hd : domT M m)
    (hop : ∀ z ∈ W m, based z → graft M z ∈ X) :
    ∀ n, 1 ≤ n → M⟦n⟧ ∈ X := by
  intro n _
  have hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0) := by
    rintro ⟨-, h1, h2⟩
    have hlev := hd.1
    unfold lev at hlev
    omega
  rw [oper_eq_pred_of_noParent n (by omega) hz hd.2]
  unfold Pred
  rw [if_neg (by omega)]
  have hres := hop [] (W_nil m) based_nil
  rwa [graft_nil] at hres

/-! ## 長さ 2 以上: `W a` 所属は展開で決まる -/

/-- **Downward**: every expansion of a `W a`-member of length ≥ 2 is again in
`W a` (the only non-clause-2 justification, clause 3, gives the same thing). -/
theorem oper_mem_of_mem {a : ℕ} {S : TrioSeq} (h2 : 2 ≤ S.length)
    (h : S ∈ W a) : ∀ n, 1 ≤ n → S⟦n⟧ ∈ W a := by
  rw [← A1 a] at h
  rcases h with ⟨hl, -⟩ | hop | ⟨m, -, hd, hop⟩
  · omega
  · exact hop
  · exact aop_clause3_to_clause2 h2 hd hop

/-- **Upward**: clause 2 is exactly the introduction rule at length ≥ 2. -/
theorem mem_of_oper_mem {a : ℕ} {S : TrioSeq}
    (h : ∀ n, 1 ≤ n → S⟦n⟧ ∈ W a) : S ∈ W a :=
  A1_intro (Or.inr (Or.inl h))

/-- The exact characterisation at length ≥ 2. -/
theorem mem_iff_oper_mem {a : ℕ} {S : TrioSeq} (h2 : 2 ≤ S.length) :
    S ∈ W a ↔ ∀ n, 1 ≤ n → S⟦n⟧ ∈ W a :=
  ⟨oper_mem_of_mem h2, mem_of_oper_mem⟩

/-! ## 長さ 1: 段はレベルの上限そのもの -/

/-- **A one-column sequence is in `W a` exactly when its level fits the
stage.**  (`←` is `Om_mem_W` + `W_shift`; `→` is `A2'` on the set of sequences
that satisfy the bound, whose clause-2 case is vacuous because `oper` is the
identity at length 1.) -/
theorem lev_le_of_mem_of_length_one {a : ℕ} {S : TrioSeq} (h1 : S.length = 1)
    (h : S ∈ W a) : lev S 0 ≤ a := by
  have hsub : W a ⊆ {T : TrioSeq | T.length = 1 → lev T 0 ≤ a} := by
    refine A2' ?_
    rintro T (⟨-, hlev⟩ | hop | ⟨m, hm, hd, -⟩) hT1
    · rw [hlev]; omega
    · have := hop 1 le_rfl
      rw [oper_of_length_one hT1 1] at this
      exact this hT1
    · have hlev := hd.1
      rw [show T.length - 1 = 0 from by omega] at hlev
      omega
  exact hsub h h1

theorem singleton_mem_W {a d v z : ℕ} (h : 2 * v + z ≤ a) :
    [((d, v, z) : ℕ × ℕ × ℕ)] ∈ W a := by
  have hs := W_shift (W_mono h (Om_mem_W v z)) d
  rwa [show shiftr01 d 0 [((0, v, z) : ℕ × ℕ × ℕ)] = [((d, v, z) : ℕ × ℕ × ℕ)]
    from by unfold shiftr01; simp] at hs

/-- The exact characterisation at length 1. -/
theorem mem_iff_lev_le {a d v z : ℕ} :
    [((d, v, z) : ℕ × ℕ × ℕ)] ∈ W a ↔ 2 * v + z ≤ a := by
  refine ⟨fun h => ?_, singleton_mem_W⟩
  have hres := lev_le_of_mem_of_length_one (by simp) h
  rw [show lev [((d, v, z) : ℕ × ℕ × ℕ)] 0 = 2 * v + z from rfl] at hres
  exact hres

end TRIO
