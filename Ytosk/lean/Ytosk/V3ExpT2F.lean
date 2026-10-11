/-
**3 行・t = 2: M[n] の値の欄（Good3 以外）。**

- `depS_ge`: 最後の根 R の木の中の種に依存する呼び出しは R 以後。
- 根の欄: rootP は一般形 `rootP_of_below`（x より前で D の外は変わらず、x の根だけが下がる）。
-/
import Ytosk.V3ExpT2I
import Ytosk.V3Root
import Ytosk.V3RootPN

namespace Ytosk

open T

/-! ## 依存の閉包は最後の根の木の中 -/

/-- **The calls depending on seeds in the tree of the last root `R` are in that tree.** -/
theorem depS_ge {M : Mat} {S : Bool → Nat → Prop} {R x : Nat} (hx : x + 1 = M.length)
    (hR0 : entry M 0 R = 0) (hRlast : ∀ j, R < j → j ≤ x → entry M 0 j ≠ 0)
    (hS : ∀ b i, S b i → R ≤ i) {b : Bool} {i : Nat} (h : DepS M S b i) : R ≤ i := by
  induction h with
  | seed hs => exact hS _ _ hs
  | @ochild i c hc _ _ _ ih =>
    have hpc := (mem_children_iff.mp hc).2
    have hcl := (mem_children hc).2
    rcases Nat.eq_or_lt_of_le ih with heq | hlt
    · subst heq; exact absurd hpc (par0_root_none hR0)
    · exact par0_ge_root hR0 hRlast hlt (by omega) hpc
  | ov _ ih => exact ih
  | @vpar i m _ hm _ ih =>
    have := par_lt M 1 i m hm; omega
  | @vupg i k _ _ hu _ ih =>
    have hle := upg_le hu
    rcases Nat.lt_or_ge k (i + 1) with h1 | h1
    · omega
    · have hk : k = i + 1 := by omega
      subst hk
      have := upg_next_e0 hu
      rcases Nat.eq_or_lt_of_le ih with heq | hlt
      · rw [← heq] at this; exact absurd hR0 this
      · omega
  | @vbump i j k _ _ hj _ hk _ ih =>
    have hpk := (mem_children_iff.mp hk).2
    have hpj := (mem_children_iff.mp hj).2
    have hkl := (mem_children hk).2
    have hjl := (mem_children hj).2
    have hjk := (mem_children hk).1
    rcases Nat.eq_or_lt_of_le ih with heq | hlt
    · subst heq; exact absurd hpk (par0_root_none hR0)
    · have hRj := par0_ge_root hR0 hRlast hlt (by omega) hpk
      rcases Nat.eq_or_lt_of_le hRj with heq | hlt2
      · subst heq; exact absurd hpj (par0_root_none hR0)
      · exact par0_ge_root hR0 hRlast hlt2 (by omega) hpj

/-- **The root values of a new matrix do not increase** when the roots are those of `M`, the values off
the closure `DepS M S` (seeds in the tree of the last root `Rt` of `x`) are unchanged, and `o(Rt)` does
not increase. -/
theorem rootP_of_below {M N : Mat} {S : Bool → Nat → Prop} {ρ σ : Valn} {x Rt : Nat}
    (hx : x + 1 = M.length) (hroots : roots N = roots M) (hRA : Anc0 M Rt x)
    (hR0 : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ x → entry M 0 j ≠ 0)
    (hS : ∀ b i, S b i → Rt ≤ i) (hoff : ∀ i, i < Rt → ¬ DepS M S true i → σ.o i = ρ.o i)
    (hle : σ.o Rt ≤ ρ.o Rt) (hpM : RootP M ρ) : RootP N σ := by
  have hR0e : entry M 0 Rt = 0 := by unfold entry; unfold col at hR0; rw [hR0]; rfl
  have hsplit := roots_split hx hRA hR0
  set pre := (roots M).filter (fun c => decide (c < Rt)) with hpre
  have hpre_lt : ∀ c ∈ pre, c < Rt := by
    intro c hc; rw [hpre, List.mem_filter] at hc; simpa using hc.2
  have hpre_nd : ∀ c ∈ pre, ¬ DepS M S true c := by
    intro c hc hd
    have := depS_ge hx hR0e hRlast hS hd
    have := hpre_lt c hc; omega
  have hN : (roots N).map σ.o = pre.map ρ.o ++ [σ.o Rt] := by
    rw [hroots, hsplit, List.map_append, List.map_singleton]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact hoff c (hpre_lt c hc) (hpre_nd c hc)
  have hMl : (roots M).map ρ.o = pre.map ρ.o ++ [ρ.o Rt] := by
    rw [hsplit, List.map_append, List.map_singleton]
  unfold RootP at hpM ⊢
  rw [hMl] at hpM
  rw [hN]
  rw [List.pairwise_append] at hpM ⊢
  refine ⟨hpM.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
  rw [List.mem_singleton] at hb; subst hb
  exact le_trans hle (hpM.2.2 a ha _ (List.mem_singleton_self _))

end Ytosk
