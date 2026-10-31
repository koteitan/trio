/-
**WfT2X6: `VSmallF` across the fourth frame case (2026-11-01, t = 2 Bad2 route).**

`vs_changed_boundV`: `vs_changed_bound` (V3VSF) with the subscript lowered by `◁_a` (`a` the frame's own `v`) in place
of `◁`. At level `a` the allowance adds nothing (`comps a a = []`), so the proof is the same.
`qVSF_of_shapeX`: `qVSF_of_shape` (V3T2VSF) with `FrameShapeX`.
-/
import Ytosk.WfT2X5
import Ytosk.V3T2VSF

namespace Ytosk.WfT2X

open T Classical Ytosk.WfAbsW

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

theorem vs_changed_boundV {a B s s' : T} (ha : isOT a = true) (hs'ot : isOT s' = true) (hl : Lhd a s' s)
    (hBc : ∀ q ∈ summands B, psi s z z ≤ q)
    (hsub : ∀ g ∈ comps a s, g ≤ psi s z z ∨ g ≤ B)
    (hot : isOT (psi a (step a B s z z) z) = true) :
    ∀ g ∈ comps a s', g ≤ psi s' z z ∨ g ≤ B := by
  intro g hg
  by_cases hB : B = z
  · subst hB
    have hst : step a z s z z = psi s z z := by
      unfold step; rw [if_neg (fun h => T.not_lt_z _ h.1)]; rfl
    rw [hst] at hot
    have hot' : isOT (psi a (psi s' z z) z) = true :=
      psi_ot_of_lhd ha (isOT_psi_zz hs'ot) (lhd_sub_eta hl) ((isOT_psi_iff).mp hot).2.2.2.2
        (fun _ g hg => by rw [comps_self_nil ha] at hg; simp at hg)
    by_cases hsa : s' < a
    · rw [comps_nil_of_lt hs'ot hsa] at hg; simp at hg
    · have hall := ((isOT_psi_iff).mp hot').2.2.2.2
      left
      apply le_of_lt
      apply hall g
      rw [comps_psi_z_of_ge hsa]
      simp [hg]
  · right
    obtain ⟨d, hd, hgd⟩ := hl.2 a s hl.1 (le_refl s) g hg
    rcases List.mem_append.mp hd with hd | hd
    · rcases hsub d hd with h | h
      · exact le_trans hgd (le_trans h (le_of_summands_ge hB hBc))
      · exact le_trans hgd h
    · simp only [Gc, List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact le_trans hgd (z_le _)
      · rw [comps_self_nil ha] at hd; simp at hd

/-- **`qVSF_of_shape` (V3T2VSF) with `FrameShapeX`.** -/
theorem qVSF_of_shapeX {M N : Mat} {ρ σ : Valn} {i : Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hCN : Cons N σ) (hGN : Good3 N σ) (hi : i < M.length) (hS : FrameShapeX M N ρ σ i)
    (hVM : VSmallF M ρ) :
    ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL N i = Lc ++ c :: R → QVSF (σ.v i) (Lc.map σ.o) (σ.o c) := by
  rcases hS with hS | ⟨hv, Lc0, c0, hclM, hclN, hsame, hoN, hoM, hVl, hOl, hoi⟩
  · exact qVSF_of_shape hC hG hCN hGN hi hS hVM
  have hQ : ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R →
      QVSF (ρ.v i) (Lc.map ρ.o) (ρ.o c) :=
    fun Lc c R h => clField_of_vsmallF hC hG hVM i hi Lc c R h
  intro Lc c R hCL
  rcases shape4_split hclM hclN hsame hCL with ⟨rfl, rfl, rfl⟩ | ⟨hCLM, hLm, hoc⟩
  · rw [hv, List.map_congr_left hsame]
    have hcN : c < N.length := (mem_children (cl_mem_children (show c ∈ CL N i by rw [hclN]; simp))).2
    intro s y hsy g hg
    rw [hoN] at hsy; simp only [psi.injEq] at hsy
    rw [← hsy.1] at hg ⊢
    obtain ⟨hsM, hpM⟩ := cl_vals hC hG hi
    rw [hclM, List.map_append, List.map_singleton] at hsM hpM
    have hLs := sumN_dec (Lc.map ρ.o) (fun t ht => hsM t (List.mem_append_left _ ht))
      (List.pairwise_append.mp hpM).1
    have hBc : ∀ q ∈ summands (spArg (ρ.v i) z (sumN (Lc.map ρ.o))), psi (ρ.v c) z z ≤ q := by
      apply spArg_summands_ge ⟨_, _, rfl⟩ (sumN (Lc.map ρ.o)) z hLs.1
      · rw [hLs.2]; intro q hq; rw [← hoM]
        exact (List.pairwise_append.mp hpM).2.2 q hq _ (by simp)
      · simp [summands]
    have hot0 : isOT (psi (ρ.v i) (step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) (ρ.v c) z z) z)
        = true := by
      have hfm := o_last_form hC hi (hG.ot_v i hi) hclM (fun d hd => single_o hC hG
        (mem_children (cl_mem_children hd)).2) (by
          rw [hclM, List.map_append, List.map_singleton]; exact hpM) hoM
      rw [← hfm]
      exact hG.ot_o i hi
    exact vs_changed_boundV (hG.ot_v i hi) (hGN.ot_v c hcN) hVl hBc (hQ Lc c [] hclM (ρ.v c) z hoM) hot0 g hg
  · rw [hv, hLm, hoc]; exact hQ Lc c R hCLM

end Ytosk.WfT2X
