/-
Finite summand support is sufficient for component domination. The support
of a row-2-zero value follows from the support of its two vRhs inputs.
-/
import Ytosk.V3HUACZero

namespace Ytosk.HUACSupport
open T

/-- Ignore multiplicity and allow extra copies of one. -/
def Support (A B : T) : Prop := ∀ q ∈ summands A, q = one ∨ q ∈ summands B

theorem support_zero (B : T) : Support z B := by simp [Support, summands]
theorem support_one (B : T) : Support one B := by simp [Support, one, summands]

/-- Addition only removes summands; the two input support bounds suffice. -/
theorem support_add {A C B : T} (hA : Support A B) (hC : Support C B) : Support (add A C) B := by
  obtain ⟨P, hP, hPs⟩ := add_eq_app_prefix A C
  intro q hq
  rw [hP, summands_app] at hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hA q (hPs q hq)
  · exact hC q hq

/-- Finite support is sufficient at every component level. -/
theorem dom_of_support {A B : T} (hs : Support A B) :
    ∀ u, Dom (comps u A) (comps u B ++ [z]) := by
  intro u g hg
  obtain ⟨q, hq, hg⟩ := comps_sub_summands u A g hg
  rcases hs q hq with rfl | hq
  · exact ⟨z, List.mem_append_right _ (by simp), by simp [comps_one_eq hg]⟩
  · exact ⟨g, List.mem_append_left _ (comps_summand_subH u hq g hg), le_refl _⟩

/-- The support of a row-2-zero value follows separately from its parent and increment. -/
theorem support_value_of_inputs {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
    {m : Nat} {B : T} (hm : m < M.length) (hm2 : entry M 2 m = 0)
    (hparent : Support (vOpt ρ (par M 1 m)) B)
    (htail : ∀ t, upg M m = some t → Support (last (ρ.v t)) B) : Support (ρ.v m) B := by
  rw [(hC m hm).2]
  unfold vRhs
  by_cases hm1 : entry M 1 m = 0
  · rw [if_pos hm1]
    exact support_zero B
  · rw [if_neg hm1, if_pos hm2]
    have hpOT := vOpt_ot hG hm
    cases hu : upg M m with
    | none =>
      rw [sf_ot (isOT_add hpOT isOT_one)]
      exact support_add hparent (support_one B)
    | some t =>
      rw [sf_ot (isOT_add hpOT (isOT_last (hG.ot_v t (upg_lt hm hu))))]
      exact support_add hparent (htail t hu)

/-- A support bound in the head index gives a bound in the whole psi term. -/
theorem dom_of_index_support {A s b : T} (hs : isOT s = true) (h : Support A s) :
    ∀ u, Dom (comps u A) (comps u (psi s b z) ++ [z]) :=
  HUACPath.comp_dom_trans (dom_of_support h) (HUACPath.index_comp_dom hs)

/-- Only absorbed summands require a new component certificate. -/
theorem dom_add_of_absorbed {A B : T} (hA : isOT A = true)
    (hdrop : ∀ q ∈ summands A, q < B →
      ∀ u, Dom (comps u q) (comps u B ++ [z])) :
    ∀ u, Dom (comps u A) (comps u (add A B) ++ [z]) := by
  induction A with
  | z => intro u g hg; simp [comps] at hg
  | psi s a c _ _ ihc =>
    cases B with
    | z => simpa only [add_z_right] using (fun u g hg => ⟨g, List.mem_append_left _ hg, le_refl g⟩)
    | psi v b d =>
      intro u g hg
      by_cases hlt : psi s a z < psi v b z
      · have hhead : psi s a z < psi v b d := lt_of_lt_of_le hlt (by simpa only [head] using head_le_self (psi v b d))
        have hadd : add (psi s a c) (psi v b d) = psi v b d := by
          simp only [add, if_pos (show lt (psi s a z) (psi v b z) = true from hlt)]
        obtain ⟨q, hq, hgq⟩ := comps_sub_summands u (psi s a c) g hg
        obtain ⟨e, he, hge⟩ := hdrop q hq (lt_of_le_of_lt (summands_le_head hA q hq) hhead) u g hgq
        exact ⟨e, by simpa only [hadd] using he, hge⟩
      · have hadd : add (psi s a c) (psi v b d) = psi s a (add c (psi v b d)) := by
          simp only [add, if_neg (show ¬ lt (psi s a z) (psi v b z) = true from hlt)]
        rw [hadd]
        simp only [comps, List.mem_append] at hg
        rcases hg with hg | hg
        · exact ⟨g, List.mem_append_left _ (by simp only [comps, List.mem_append]; exact Or.inl hg), le_refl _⟩
        · obtain ⟨e, he, hge⟩ := ihc (isOT_rest hA)
            (fun q hq => hdrop q (by simp only [summands, List.mem_cons]; exact Or.inr hq)) u g hg
          refine ⟨e, ?_, hge⟩
          rcases List.mem_append.mp he with he | he
          · exact List.mem_append_left _ (by simp only [comps, List.mem_append]; exact Or.inr he)
          · exact List.mem_append_right _ he

/-- Finite support is needed only for the summands actually absorbed by W. -/
def AbsorbedSupport (A W : T) : Prop :=
  ∀ q ∈ summands A, q < W → q = one ∨ q ∈ summands (lev W)

/-- A support bound only on absorbed summands suffices for the whole addition. -/
theorem dom_add_of_support {A s b : T} (hA : isOT A = true)
    (hs : isOT s = true) (h : AbsorbedSupport A (psi s b z)) :
    ∀ u, Dom (comps u A) (comps u (add A (psi s b z)) ++ [z]) := by
  apply dom_add_of_absorbed hA
  intro q hq hlt u g hg
  rcases h q hq hlt with rfl | hq
  · exact ⟨z, List.mem_append_right _ (by simp), by simp [comps_one_eq hg]⟩
  · exact HUACPath.index_comp_dom hs u g (comps_summand_subH u hq g hg)

/-- A whole-input support bound implies the weaker absorbed-input bound. -/
theorem absorbed_of_support {A W : T} (h : Support A (lev W)) : AbsorbedSupport A W :=
  fun q hq _ => h q hq

/-- The value equation at an actual upgrade target, without a support assumption. -/
theorem value_at_target {M : Mat} {ρ : Valn} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ)
    {n k : Nat} (hn : n < M.length) (hu : upg M n = some k) :
    ρ.v n = add (vOpt ρ (par M 1 n)) (bumpW M ρ k) := by
  obtain ⟨h1n, h2n'⟩ := upg_e12 hu
  have h2n : entry M 2 n = 0 := by have := S.z2 n; omega
  have hkN := upg_lt hn hu
  obtain ⟨m, hmn, hmk, hcol, _⟩ := upg_spec hu
  have h1k : entry M 1 k ≠ 0 := by have := e1_of_col hcol; omega
  have h2k : entry M 2 k ≠ 0 := by have := e2_of_col hcol; omega
  have hVot := vOpt_ot hG hn
  rw [v_upg_eq hC hn h1n h2n hu hVot (fun _ _ _ d hd => hG.ot_o d (mem_children hd).2)]
  rw [(hC k hkN).2]
  unfold vRhs bumpW
  rw [if_neg h1k, if_neg h2k, hmk, hmn]
  exact sf_ot (isOT_add (by simpa only [hmn] using hVot) (isOT_omega (isOT_bumpP hG k)))

/-- In an actual upgrade frame only finite support of absorbed summands remains. -/
theorem dom_of_absorbed_support {M : Mat} {ρ : Valn} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ)
    {n k : Nat} (hn : n < M.length) (hu : upg M n = some k)
    (h : AbsorbedSupport (vOpt ρ (par M 1 n)) (bumpW M ρ k)) :
    ∀ u, Dom (comps u (vOpt ρ (par M 1 n))) (comps u (ρ.v n) ++ [z]) := by
  have hv := value_at_target S hC hG hn hu
  obtain ⟨s, b, hW⟩ := omega_psi_form (sumN (one :: (children M k).map (bumpTerm M ρ k)))
  change bumpW M ρ k = psi s b z at hW
  rw [hv, hW]
  rw [hW] at h
  have hs : isOT s = true := isOT_sub (by rw [← hW]; exact isOT_omega (isOT_bumpP hG k))
  exact dom_add_of_support (vOpt_ot hG hn) hs h

/-- A plain finite support residual, only at positive absent-return frames and
only for the old summands absorbed by the new bump term. This does not assert
support for unabsorbed old summands, which already survive in the sum. -/
def HUACAbsSupport : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Rk N rk → Good3 N σ →
    ∀ n k m, upg N n = some k → k < n → par N 0 k = some m →
      ¬ HUACCopy.ReturnWitness N n k m → lev (bumpW N σ k) ≠ z →
      AbsorbedSupport (vOpt σ (par N 1 n)) (bumpW N σ k)

/-- All component quantifiers are derived from finite support of absorbed inputs. -/
theorem hUACPositive_of (hU : HUACAbsSupport) : HUACZero.HUACPositive := by
  intro N σ rk hN hS hC hR hG n k m hu hkn hkm hw hpos
  exact dom_of_absorbed_support (sInv_std hN hS) hC hG
    (by have := upg_succ_lt hu; omega) hu (hU N σ rk hN hS hC hR hG n k m hu hkn hkm hw hpos)

/-- Only absorbed summands with a nonzero level-zero component need support.
At higher levels comps_anti supplies the same zero-only test. -/
def ActiveSupport (A W : T) : Prop :=
  ∀ q ∈ summands A, q < W → (∃ g ∈ comps z q, g ≠ z) → q ∈ summands (lev W)

/-- Summands with only zero components never require a support certificate. -/
theorem dom_add_of_active_support {A s b : T} (hA : isOT A = true)
    (hs : isOT s = true) (h : ActiveSupport A (psi s b z)) :
    ∀ u, Dom (comps u A) (comps u (add A (psi s b z)) ++ [z]) := by
  apply dom_add_of_absorbed hA
  intro q hq hlt u g hg
  by_cases hgz : g = z
  · exact ⟨z, List.mem_append_right _ (by simp), by simp [hgz]⟩
  · have hq' := h q hq hlt ⟨g, comps_anti (z_le u) hg, hgz⟩
    exact HUACPath.index_comp_dom hs u g (comps_summand_subH u hq' g hg)

end Ytosk.HUACSupport
