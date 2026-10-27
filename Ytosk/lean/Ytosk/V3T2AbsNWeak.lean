/-
The weak branch actually needed at a failed drop absorption (2026-10-27).
BumpAbsCB supplies its shape; no additional residual is introduced here.
-/
import Ytosk.V3T2BelowR

namespace Ytosk.T2AbsNWeak

open T

set_option linter.unusedSectionVars false

/-- At a failed drop absorption, the existing bump hypothesis supplies the weak shape. -/
theorem weak_of_drop_failure {M : Mat} {x q i : Nat} {ρ τ : Valn}
    (hAbs : BumpAbsCB M x ρ) (hτ : Cons (M.take x) τ)
    (hpx : par M 0 x = some q)
    (hqb : ∀ j, par M 0 q = some j → col M q ≠ bump M j)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    (hfail : ¬ (∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z →
      ¬ s < bumpW (M.take x) τ i → s < bumpW M ρ i → Lhd z s (bumpW M ρ i))) :
    WkVA (τ.v i) (ρ.v i) ∧ WCSP M ρ i (τ.v i) ∧ CntX M ρ i := by
  have h := hAbs τ hτ i h1 h2 (fun j hj hjb hjx => by
    exfalso
    have hxj : x ∈ children M j := by rw [hjx]; simp
    have hpx' := (mem_children_iff.mp hxj).2
    rw [hpx] at hpx'; cases hpx'
    exact hqb i (mem_children_iff.mp hj).2 hjb)
    (Or.inr (Or.inl (by
      intro q' j hq' hj
      rw [hpx] at hq'; cases hq'
      exact hqb j hj)))
  rcases h with h | h
  · exact False.elim (hfail (fun s hs _ hn hlt => h s hs hn hlt))
  · exact h

/-- Outside the weak branch the source-to-prefix absorption needs no new input. -/
theorem absorption_of_weak_branch {M N : Mat} {x q i : Nat} {ρ τ σ : Valn}
    (hAbs : BumpAbsCB M x ρ) (hτ : Cons (M.take x) τ)
    (hpx : par M 0 x = some q)
    (hqb : ∀ j, par M 0 q = some j → col M q ≠ bump M j)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    (hmono : bumpW (M.take x) τ i ≤ bumpW N σ i)
    (hweak : WkVA (τ.v i) (ρ.v i) → WCSP M ρ i (τ.v i) → CntX M ρ i →
      ∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z →
        ¬ s < bumpW N σ i → s < bumpW M ρ i → Lhd z s (bumpW M ρ i)) :
    ∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z →
      ¬ s < bumpW N σ i → s < bumpW M ρ i → Lhd z s (bumpW M ρ i) := by
  classical
  by_cases hdrop : ∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z →
      ¬ s < bumpW (M.take x) τ i → s < bumpW M ρ i → Lhd z s (bumpW M ρ i)
  · intro s hs hs2 hn hlt
    exact hdrop s hs hs2 (fun h => hn (lt_of_lt_of_le h hmono)) hlt
  · obtain ⟨hw, hc, hx⟩ := weak_of_drop_failure hAbs hτ hpx hqb h1 h2 hdrop
    exact hweak hw hc hx

end Ytosk.T2AbsNWeak
