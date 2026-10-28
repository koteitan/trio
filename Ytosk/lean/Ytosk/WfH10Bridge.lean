/-
H10Big from a structural statement about the upgrade target of x - 1.

In the frame of T0BadSeedsH10Big, Bad2's shape forces the grandparent of x - 1
to be an ancestor of x.  When the upgrade target k of x - 1 has no bump child,
bumpW k = ω, so every absorbed summand is finite and the strong absorption at
x holds.  This contradicts Bad2.  No value hypothesis is assumed.

KNoBump is FALSE on standard matrices (2,606 standard grafts; e.g. WfH10Cex.M,
where k = 18 has the bump child 19).  H10Big itself fails on WfH10Cex.M, so this
bridge only records the reduction; it is not a route to eliminate H10Big.
-/
import Ytosk.V3T0H10Core
import Ytosk.V3T2UpgAbs
import Ytosk.V3SibCol

namespace Ytosk.WfH10
open T

/-- **Residual candidate**: in the H10Big frame with both upgrades and Bad2's
bump-parent shape, the upgrade target of `x - 1` has no bump child. -/
def KNoBump : Prop :=
  ∀ M, Std M → M ≠ SRO → ∀ r L g, T0H10Core.Frame M r L g → 2 ≤ entry M 1 g →
    upg M (r - 1) = some r → ∀ k, upg M (r + L - 1) = some k →
    ∀ p b, par M 0 (r + L - 1) = some p → par M 0 p = some b → col M p = bump M b →
      Anc0 M b (r + L) →
      ∀ j ∈ children M k, col M j ≠ bump M k

/-- Without a bump child, the bump value of `k` is `ω`. -/
theorem bumpW_of_no_bump {M : Mat} {ρ : Valn} {k : Nat}
    (h : ∀ j ∈ children M k, col M j ≠ bump M k) : bumpW M ρ k = omega one := by
  unfold bumpW
  have hz : ∀ t ∈ (children M k).map (bumpTerm M ρ k), t = z := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
    unfold bumpTerm
    rw [if_neg (h j hj)]
  rw [sumN_one_zeros hz, sumN_singleton (t := one) ⟨rfl, z, z, rfl⟩]

theorem omega_one_lt_E0 : omega one < E0 := by
  rw [omega_small one_lt_E0]
  exact lt_E0_iff.mpr ⟨rfl, by decide⟩

/-- The strong absorption at `x` when the upgrade target of `x - 1` has no bump child. -/
theorem strong_of_no_bump {M : Mat} {ρ : Valn} {x k : Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hu : upg M (x - 1) = some k)
    (hnb : ∀ j ∈ children M k, col M j ≠ bump M k) : UpgAbsX M x ρ := by
  intro i k' W hix hu' hv hW q hq hlt
  have hi : i = x - 1 := by omega
  subst hi
  rw [hu] at hu'
  cases hu'
  have hiM : x - 1 < M.length := by have := upg_succ_lt hu; omega
  have hV := vOpt_ot hG hiM
  obtain ⟨_, _, _, _, hvk, _⟩ := upg_target_val hC hG hiM hu
  rw [bumpW_of_no_bump hnb] at hvk
  have hEq : W = omega one := T2UpgAbs.add_right_injective _ (hv.symm.trans hvk)
  rw [hEq] at hlt ⊢
  exact lhd_lt_small (isOT_mem_summands hV hq) omega_one_lt_E0 hlt

/-- `UpgAbsX` depends only on the values at columns of `M`. -/
theorem upgAbsX_congr {M : Mat} {ρ σ : Valn} {x : Nat}
    (hEq : ∀ i, i < M.length → ρ.v i = σ.v i) (h : UpgAbsX M x ρ) : UpgAbsX M x σ := by
  intro i k W hix hu hv hW q hq hlt
  have hiM : i < M.length := by have := upg_succ_lt hu; omega
  have hkM : k < M.length := upg_lt hiM hu
  have hpar : vOpt σ (par M 1 i) = vOpt ρ (par M 1 i) := by
    cases hp : par M 1 i with
    | none => rfl
    | some m =>
      have := par_lt M 1 i m hp
      simp only [vOpt]
      exact (hEq m (by omega)).symm
  rw [hpar] at hv hq
  rw [← hEq k hkM] at hv
  exact h i k W hix hu hv hW q hq hlt

/-- **Bridge**: the structural residual `KNoBump` proves `T0BadSeedsH10Big`. -/
theorem h10Big_of_kNoBump (hK : KNoBump) : T0H10Core.T0BadSeedsH10Big := by
  intro M ρ rk hM hNe hBad I r L hlen hL hp he g hg hbig hr hn hc ht hu
  have F : T0H10Core.Frame M r L g := ⟨hlen, hL, hp, he, hg, hr, hn, hc, ht⟩
  have S := sInv_std hM hNe
  have hlength : M.length - 1 = r + L := by omega
  have hlength' : M.length - 2 = r + L - 1 := by omega
  obtain ⟨⟨k, hk⟩, p, b, hp', hb, hcol, hbad⟩ := hBad
  rw [hlength'] at hk hp'
  rcases hbad with ⟨hanc, σ, hσ, hnot⟩ | hbad
  · have hA : Anc0 M b (r + L) := by
      rw [hlength] at hanc
      rcases hanc with h | h
      · exact h
      · exact False.elim (h (S.r12 _ he))
    have hnb := hK M hM hNe r L g F hbig hu k hk p b hp' hb hcol hA
    have hs : UpgAbsX M (r + L) ρ := by
      have hk' : upg M (r + L - 1) = some k := hk
      exact strong_of_no_bump I.cons I.good hk' hnb
    have hEq : ∀ i, i < M.length → ρ.v i = σ.v i :=
      fun i hi => (cons_unique I.cons hσ I.rank i hi).2
    rw [hlength] at hnot
    exact hnot (upgAbsX_congr hEq hs)
  · have hne := hbad.2.1
    rw [hlength] at hne
    exact hne he

end Ytosk.WfH10
