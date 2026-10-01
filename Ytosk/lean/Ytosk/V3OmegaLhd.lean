/-
**ω^ は ◁ を保つ**（落とす補題ののりしろの枠で使う）。
-/
import Ytosk.V3DropV

namespace Ytosk

open T

/-- `1 ≤ ω^X`. -/
theorem one_le_omega {X : T} (hX : isOT X = true) : one ≤ omega X := by
  by_cases h : X = z
  · subst h; right; rfl
  · have := omega_lt_omega (x := z) rfl hX (by cases X with | z => exact absurd rfl h | psi => exact T.z_lt_psi _ _ _)
    exact Or.inl this

/-- **The emptied sum**: `ω^0 = 1 ⊴ ω^X`. -/
theorem omega_lhd_z {X : T} (hX : isOT X = true) : LhdE (omega z) (omega X) :=
  lhdE_one (one_le_omega hX)

/-- **Case 1, below `ψ_0(Ω_1)`**: `ω^x = ψ_0(x)`. -/
theorem omega_lhd_small {X' X : T} (h : LhdE X' X) (hX' : X' < E0) (hX : X < E0) :
    LhdE (omega X') (omega X) := by
  rw [omega_small hX', omega_small hX]; exact lhdE_psi z h

/-- **Case 2, tail change**: the same leading summand `ψ_s(b)`, the tails `c′ ⊴ c`. -/
theorem omega_lhd_tail {s b c' c : T} (hX' : isOT (psi s b c') = true) (hX : isOT (psi s b c) = true)
    (hE : ¬ psi s b z < E0) (hc : LhdE c' c) : LhdE (omega (psi s b c')) (omega (psi s b c)) := by
  have hE' : ∀ {e}, ¬ psi s b e < E0 := fun he => hE (by
    obtain ⟨rfl, hb⟩ := below_E0 he
    unfold E0; rw [T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, hb⟩))
  rw [omega_big hX' hE', omega_big hX hE']
  by_cases hlo : (split b (psi (succ s) z z)).2 = z
  · rw [if_pos hlo, if_pos hlo]; exact lhdE_psi s (lhdE_app _ hc)
  · rw [if_neg hlo, if_neg hlo]
    apply lhdE_psi s; apply lhdE_app
    have := lhdE_app (psi s b z) hc
    simpa using this

/-! ## 反例: 先頭の添字が上がると成り立たない -/

/-- `Ω_1 + Ω_1`. -/
def cxX' : T := psi one z (psi one z z)
/-- `Ω_2`. -/
def cxX : T := psi (psi z z one) z z

theorem cx_lhd : Lhd z cxX' cxX := by
  refine ⟨by decide, fun u c _ _ g hg => ⟨z, by simp [Gc], ?_⟩⟩
  have : g = z := by
    simp only [cxX', one, comps] at hg
    split_ifs at hg <;> simp_all
  subst this; exact le_refl _

/-- **`ω^` does not preserve `◁` when the leading subscript grows**:
`Ω_1·2 ◁ Ω_2` but `ω^(Ω_1·2) = ψ_1(Ω_1)` is not `⊴ ω^(Ω_2) = Ω_2`. -/
theorem omega_lhd_counterexample :
    isOT cxX' = true ∧ isOT cxX = true ∧ LhdE cxX' cxX ∧ ¬ cxX' < E0 ∧
      ¬ LhdE (omega cxX') (omega cxX) := by
  refine ⟨by decide, by decide, Or.inr cx_lhd, by decide, ?_⟩
  have h1 : omega cxX' = psi one (psi one z z) z := by decide
  have h2 : omega cxX = cxX := by decide
  rw [h1, h2]
  rintro (h | h)
  · exact absurd h (by decide)
  · obtain ⟨y, hy, hle⟩ := h.2 z cxX h.1 (le_refl _) (psi one z z) (by decide)
    revert hle; revert hy; revert y; decide

end Ytosk
