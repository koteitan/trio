/-
**WfSdH4: `BumpAbsCB` with `WCSP2` (2026-11-01).**

`BumpAbsCB` (V3BumpDropB) is the bump absorption of the drop lemma: the strong absorption at `i`, or the weak route of
`PV` at `i` (`WkVA`, `WCSP`, `CntX`). `PV` itself is false on graftE (901 times) while `PV2` (with `WCSP2`, WfDrE1)
holds; `BumpAbsCB2` is the same with `WCSP2`. It is implied by `BumpAbsCB` (`BumpAbsCB.toB2`).
Measured (tmp/wf/WfSdH/abcb2.py, notes.md).
- `weak_of_drop_failure2`, `absorption_of_weak_branch2`: `T2AbsNWeak.weak_of_drop_failure` /
  `absorption_of_weak_branch` with `BumpAbsCB2` (they return `WCSP2`).
-/
import Ytosk.WfDrE1
import Ytosk.V3T2AbsNWeak

namespace Ytosk

open T

/-- **`BumpAbsCB` with `WCSP2`**: the strong absorption, or the weak route of `PV2` at `i`. -/
def BumpAbsCB2 (M : Mat) (x : Nat) (ρ : Valn) : Prop :=
  ∀ σ', Cons (M.take x) σ' → ∀ i, entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
    (∀ j ∈ children M i, col M j = bump M i → children M j = [x] → ρ.v x = z) →
    (StrongG M x ρ i ∨ XParNB M x ∨ ρ.v x = z) →
    (∀ r ∈ summands (vOpt ρ (par M 1 i)), ¬ r < bumpW (M.take x) σ' i → r < bumpW M ρ i →
        Lhd z r (bumpW M ρ i)) ∨
      (WkVA (σ'.v i) (ρ.v i) ∧ WCSP2 M ρ i (σ'.v i) ∧ CntX M ρ i)

/-- `BumpAbsCB` gives `BumpAbsCB2`. -/
theorem BumpAbsCB.toB2 {M : Mat} {x : Nat} {ρ : Valn} (h : BumpAbsCB M x ρ) : BumpAbsCB2 M x ρ :=
  fun σ' hσ i h1 h2 hx hg =>
    (h σ' hσ i h1 h2 hx hg).imp id (fun ⟨hw, hc, hx⟩ => ⟨hw, hc.toWCSP2 hw.2.1, hx⟩)

/-- `BumpAbsC` gives `BumpAbsCB2`. -/
theorem BumpAbsC.toB2 {M : Mat} {x : Nat} {ρ : Valn} (h : BumpAbsC M x ρ) : BumpAbsCB2 M x ρ :=
  h.toB.toB2

namespace T2AbsNWeak

/-- **`weak_of_drop_failure` with `BumpAbsCB2`**: at a failed drop absorption, the weak shape with `WCSP2`. -/
theorem weak_of_drop_failure2 {M : Mat} {x q i : Nat} {ρ τ : Valn}
    (hAbs : BumpAbsCB2 M x ρ) (hτ : Cons (M.take x) τ)
    (hpx : par M 0 x = some q)
    (hqb : ∀ j, par M 0 q = some j → col M q ≠ bump M j)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    (hfail : ¬ (∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z →
      ¬ s < bumpW (M.take x) τ i → s < bumpW M ρ i → Lhd z s (bumpW M ρ i))) :
    WkVA (τ.v i) (ρ.v i) ∧ WCSP2 M ρ i (τ.v i) ∧ CntX M ρ i := by
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

/-- **`absorption_of_weak_branch` with `BumpAbsCB2`** (the weak branch now carries `WCSP2`). -/
theorem absorption_of_weak_branch2 {M N : Mat} {x q i : Nat} {ρ τ σ : Valn}
    (hAbs : BumpAbsCB2 M x ρ) (hτ : Cons (M.take x) τ)
    (hpx : par M 0 x = some q)
    (hqb : ∀ j, par M 0 q = some j → col M q ≠ bump M j)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    (hmono : bumpW (M.take x) τ i ≤ bumpW N σ i)
    (hweak : WkVA (τ.v i) (ρ.v i) → WCSP2 M ρ i (τ.v i) → CntX M ρ i →
      ∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z →
        ¬ s < bumpW N σ i → s < bumpW M ρ i → Lhd z s (bumpW M ρ i)) :
    ∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z →
      ¬ s < bumpW N σ i → s < bumpW M ρ i → Lhd z s (bumpW M ρ i) := by
  classical
  by_cases hdrop : ∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z →
      ¬ s < bumpW (M.take x) τ i → s < bumpW M ρ i → Lhd z s (bumpW M ρ i)
  · intro s hs hs2 hn hlt
    exact hdrop s hs hs2 (fun h => hn (lt_of_lt_of_le h hmono)) hlt
  · obtain ⟨hw, hc, hx⟩ := weak_of_drop_failure2 hAbs hτ hpx hqb h1 h2 hdrop
    exact hweak hw hc hx

end T2AbsNWeak

end Ytosk
