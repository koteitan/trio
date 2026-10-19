/-
Local reductions for T2UpgAbsW. The complete failure-shape theorem is the
target; the lemmas below isolate the old-target and NBPar parts without
assuming the residual being investigated.
-/
import Ytosk.V3T2R2
import Ytosk.V3GroupA

namespace Ytosk.T2UpgAbs
open T

/-- Right strict monotonicity makes addition injective in its right argument,
even for arbitrary raw terms. -/
theorem add_right_injective (V : T) {W W' : T}
    (h : add V W = add V W') : W = W' := by
  rcases lt_trichotomy W W' with hlt | heq | hgt
  · have := add_lt_add_left V hlt
    rw [h] at this
    exact False.elim ((lt_irrefl _) this)
  · exact heq
  · have := add_lt_add_left V hgt
    rw [h] at this
    exact False.elim ((lt_irrefl _) this)

/-- At a leaf upgrade target, the only possible nonzero W is omega. -/
theorem absorption_at_leaf {M : Mat} {ρ : Valn} {i k : Nat} {W : T}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hi : i < M.length)
    (hu : upg M i = some k) (hLeaf : children M k = [])
    (hW : ρ.v k = add (vOpt ρ (par M 1 i)) W) :
    ∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W := by
  obtain ⟨m, hm, _, _, _⟩ := upg_spec hu
  have hV : isOT (vOpt ρ (par M 1 i)) = true := by
    rw [hm]
    exact hG.ot_v m (Nat.lt_trans (par_lt M 1 i m hm) hi)
  obtain ⟨_, _, _, _, hv, _⟩ := upg_target_val hC hG hi hu
  have hBW : bumpW M ρ k = omega one := by
    unfold bumpW
    rw [hLeaf]
    simp only [List.map_nil]
    rw [sumN_singleton (t := one) ⟨rfl, z, z, rfl⟩]
  rw [hBW] at hv
  have hEq : W = omega one := add_right_injective _ (hW.symm.trans hv)
  rw [hEq]
  intro r hr hlt
  exact lhd_lt_small (isOT_mem_summands hV hr) (by
    rw [omega_small one_lt_E0]
    exact lt_E0_iff.mpr ⟨rfl, by decide⟩) hlt

/-- Failure of strong absorption supplies an old upgrade target and NBPar.
The remaining parent-coincidence claim is not assumed in this reduction. -/
theorem old_target_of_failure {M : Mat} {ρ : Valn} {x : Nat}
    (hx : x + 1 = M.length) (hC : Cons M ρ) (hG : Good3 M ρ)
    (hUA : UpgAbsXW M x ρ) (hFail : ¬ UpgAbsX M x ρ) :
    ∃ k, upg M (x - 1) = some k ∧ k < x ∧ NBPar M (x - 1) := by
  classical
  unfold UpgAbsX at hFail
  push Not at hFail
  obtain ⟨i, k, W, hix, hu, hv, hW, r, hr, hrW, hnl⟩ := hFail
  have hi : i < M.length := by omega
  have hne : k ≠ x := by
    intro heq
    subst k
    exact hnl (absorption_at_leaf hC hG hi hu (children_last hx) hv r hr hrW)
  have hkx : k < x := by have := upg_le hu; omega
  have hnb : NBPar M i := by
    rcases hUA i k W hix hu hv hW with hs | hw
    · exact False.elim (hnl (hs r hr hrW))
    · exact hw.2.2.1
  have hie : i = x - 1 := by omega
  exact ⟨k, by simpa [hie] using hu, hkx, by simpa [hie] using hnb⟩

#print axioms absorption_at_leaf
#print axioms old_target_of_failure
end Ytosk.T2UpgAbs
