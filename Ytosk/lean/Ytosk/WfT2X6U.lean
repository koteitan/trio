/-
The `VSmallF` reader for `FrameShapeXU`.  The ordinary X case delegates to
WfT2X6; the new fifth case uses the foreign-allowance bound.
-/
import Ytosk.WfT2X5U
import Ytosk.V3T2VSF

namespace Ytosk.WfT2X

open T Classical Ytosk.WfAbsW

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- `qVSF_of_shapeX` for the widened fifth frame shape. -/
theorem qVSF_of_shapeXU {M N : Mat} {ρ σ : Valn} {i : Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hGN : Good3 N σ)
    (hi : i < M.length) (hS : FrameShapeXU M N ρ σ i) (hVM : VSmallF M ρ) :
    ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL N i = Lc ++ c :: R →
      QVSF (σ.v i) (Lc.map σ.o) (σ.o c) := by
  rcases hS with hS | ⟨hv, Lc0, c0, V, hclM, hclN, hsame, hoN, hoM, hVl, hOl, hsm, hoi⟩
  · exact qVSF_of_shapeX hC hG hCN hGN hi hS hVM
  have hQ : ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R →
      QVSF (ρ.v i) (Lc.map ρ.o) (ρ.o c) :=
    fun Lc c R h => clField_of_vsmallF hC hG hVM i hi Lc c R h
  intro Lc c R hCL
  rcases shape4_split hclM hclN hsame hCL with ⟨rfl, rfl, rfl⟩ | ⟨hCLM, hLm, hoc⟩
  · rw [hv, List.map_congr_left hsame]
    have hcN : c < N.length :=
      (mem_children (cl_mem_children (show c ∈ CL N i by rw [hclN]; simp))).2
    intro s y hsy g hg
    rw [hoN] at hsy
    simp only [psi.injEq] at hsy
    rw [← hsy.1] at hg ⊢
    obtain ⟨hsM, hpM⟩ := cl_vals hC hG hi
    rw [hclM, List.map_append, List.map_singleton] at hsM hpM
    have hLs := sumN_dec (Lc.map ρ.o) (fun t ht => hsM t (List.mem_append_left _ ht))
      (List.pairwise_append.mp hpM).1
    have hBc : ∀ q ∈ summands (spArg (ρ.v i) z (sumN (Lc.map ρ.o))),
        psi (ρ.v c) z z ≤ q := by
      apply spArg_summands_ge ⟨_, _, rfl⟩ (sumN (Lc.map ρ.o)) z hLs.1
      · rw [hLs.2]
        intro q hq
        rw [← hoM]
        exact (List.pairwise_append.mp hpM).2.2 q hq _ (by simp)
      · simp [summands]
    have hot0 : isOT (psi (ρ.v i)
        (step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) (ρ.v c) z z) z) = true := by
      have hfm := o_last_form hC hi (hG.ot_v i hi) hclM (fun d hd => single_o hC hG
        (mem_children (cl_mem_children hd)).2) (by
          rw [hclM, List.map_append, List.map_singleton]
          exact hpM) hoM
      rw [← hfm]
      exact hG.ot_o i hi
    have hsm' : ∀ g ∈ comps (ρ.v i) V, g < psi (σ.v c) z z := by
      intro g hg
      simpa only [hoN] using hsm (ρ.v i) g hg
    exact vs_changed_boundVG (hG.ot_v i hi) (hGN.ot_v c hcN) hVl hsm' hBc
      (hQ Lc c [] hclM (ρ.v c) z hoM) hot0 g hg
  · rw [hv, hLm, hoc]
    exact hQ Lc c R hCLM

end Ytosk.WfT2X
