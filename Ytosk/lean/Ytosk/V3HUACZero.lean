/-
A zero-index right summand cannot destroy component domination of a standard
left operand. This removes the zero-index cases from the HUAC residual.
-/
import Ytosk.V3HUACCopy

namespace Ytosk.HUACZero
open T

/-- Every component survives or is dominated when a zero-index term is added. -/
theorem dom_add_zero_index {A b : T} (hA : isOT A = true) :
    ∀ u, Dom (comps u A) (comps u (add A (psi z b z)) ++ [z]) := by
  induction A with
  | z => intro u g hg; simp [comps] at hg
  | psi s a c _ _ ihc =>
    intro u g hg
    by_cases hlt : psi s a z < psi z b z
    · have hadd : add (psi s a c) (psi z b z) = psi z b z := by
        simp only [add, if_pos (show lt (psi s a z) (psi z b z) = true from hlt)]
      rw [hadd]
      by_cases hu : u = z
      · subst u
        exact ⟨b, List.mem_append_left _ (comps_psi_mem_of (not_lt_z _) (Or.inl rfl)),
          comps_tail_le hA (le_of_lt hlt) g hg⟩
      · have hlev : lev (psi s a c) = z := by
          have hs : s ≤ z := lev_le_of_le (le_of_lt hlt)
          exact le_antisymm hs (z_le _)
        have hzu : z < u := by cases u with | z => exact False.elim (hu rfl) | psi => exact z_lt_psi _ _ _
        rw [OmegaComps.comps_nil_above_head hA (by rw [hlev]; exact hzu)] at hg
        simp at hg
    · have hadd : add (psi s a c) (psi z b z) = psi s a (add c (psi z b z)) := by
        simp only [add, if_neg (show ¬ lt (psi s a z) (psi z b z) = true from hlt)]
      rw [hadd]
      simp only [comps, List.mem_append] at hg
      rcases hg with hg | hg
      · refine ⟨g, List.mem_append_left _ ?_, le_refl _⟩
        simp only [comps, List.mem_append]
        exact Or.inl hg
      · obtain ⟨d, hd, hgd⟩ := ihc (isOT_rest hA) u g hg
        refine ⟨d, ?_, hgd⟩
        rcases List.mem_append.mp hd with hd | hd
        · exact List.mem_append_left _ (by simp only [comps, List.mem_append]; exact Or.inr hd)
        · exact List.mem_append_right _ hd

/-- The zero-index case of HUAC follows from the pure addition lemma. -/
theorem dom_of_zero {M : Mat} {ρ : Valn} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ)
    {n k : Nat} (hn : n < M.length) (hu : upg M n = some k)
    (hzero : lev (bumpW M ρ k) = z) :
    ∀ u, Dom (comps u (vOpt ρ (par M 1 n))) (comps u (ρ.v n) ++ [z]) := by
  obtain ⟨h1n, h2n'⟩ := upg_e12 hu
  have h2n : entry M 2 n = 0 := by have := S.z2 n; omega
  have hkN := upg_lt hn hu
  obtain ⟨m, hmn, hmk, hcol, _⟩ := upg_spec hu
  have h1k : entry M 1 k ≠ 0 := by have := e1_of_col hcol; omega
  have h2k : entry M 2 k ≠ 0 := by have := e2_of_col hcol; omega
  have hVot := vOpt_ot hG (show n < M.length by omega)
  have hnv := v_upg_eq hC hn h1n h2n hu hVot
    (fun _ _ _ d hd => hG.ot_o d (mem_children hd).2)
  obtain ⟨s, b, hW⟩ := omega_psi_form (sumN (one :: (children M k).map (bumpTerm M ρ k)))
  change lev (omega _) = z at hzero
  rw [hW] at hzero
  change s = z at hzero
  subst s
  have hkv : ρ.v k = add (vOpt ρ (par M 1 n)) (psi z b z) := by
    rw [(hC k hkN).2]
    unfold vRhs
    rw [if_neg h1k, if_neg h2k, hW, hmk, hmn]
    exact sf_ot (isOT_add (by simpa only [hmn] using hVot) (by rw [← hW]; exact isOT_omega (isOT_bumpP hG k)))
  rw [hnv, hkv]
  exact dom_add_zero_index hVot

/-- HUAC is left only for positive bump indices without a return-copy witness.
The critical zero-index family measured 1,108 occurrences and is now covered
by dom_of_zero. The 6,212 positive unequal-index occurrences remain candidates
for a finite summand-support certificate, not an assumed global inequality. -/
def HUACPositive : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Rk N rk → Good3 N σ →
    ∀ n k m, upg N n = some k → k < n → par N 0 k = some m →
      ¬ HUACCopy.ReturnWitness N n k m → lev (bumpW N σ k) ≠ z →
      ∀ u, Dom (comps u (vOpt σ (par N 1 n))) (comps u (σ.v n) ++ [z])

/-- Zero-index addition disposes of the corresponding absent-copy cases. -/
theorem hUAC'_of (hU : HUACPositive) : HUACCopy.HUAC' := by
  intro N σ rk hN hS hC hR hG n k m hu hkn hkm hw
  by_cases hzero : lev (bumpW N σ k) = z
  · exact dom_of_zero (sInv_std hN hS) hC hG (by have := upg_succ_lt hu; omega) hu hzero
  · exact hU N σ rk hN hS hC hR hG n k m hu hkn hkm hw hzero

end Ytosk.HUACZero
