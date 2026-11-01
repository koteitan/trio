/-
Frame readers for `FrameShapeXU`: the old X case delegates to WfT2X5, and
the new fifth case uses the same split argument as the old fourth case.
-/
import Ytosk.V3AbsUpgFrame
import Ytosk.WfT2X5

namespace Ytosk.WfT2X

open T Classical Ytosk.WfAbsW

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- `frame_of_shapeX` for the widened fifth frame shape. -/
theorem frame_of_shapeXU {M N : Mat} {ρ σ : Valn} {i : Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hGN : Good3 N σ)
    (hS : FrameShapeXU M N ρ σ i) {Lc : List Nat} {c : Nat} {R : List Nat}
    (hCL : CL N i = Lc ++ c :: R) {s y : T} (hsy : σ.o c = psi s y z)
    (ht : lt (spArg (σ.v i) z (sumN (Lc.map σ.o))) y = true ∧
      lt (psi (σ.v i) z z) (psi s y z) = true) :
    ∃ (Lc' R' : List Nat) (yM : T), CL M i = Lc' ++ c :: R' ∧ σ.v i = ρ.v i ∧
      Lc'.map ρ.o = Lc.map σ.o ∧ ρ.o c = psi s yM z ∧ y ≤ yM ∧
      (lt (spArg (ρ.v i) z (sumN (Lc'.map ρ.o))) yM = true ∧
        lt (psi (ρ.v i) z z) (psi s yM z) = true) := by
  rcases hS with hS | ⟨hv, Lc0, c0, V, hclM, hclN, hsame, hoN, hoM, hVl, hOl, hsm, hoi⟩
  · exact frame_of_shapeX hC hG hCN hGN hS hCL hsy ht
  rcases shape4_split hclM hclN hsame hCL with ⟨-, -, rfl⟩ | ⟨hCLM, hLm, hoc⟩
  · exfalso
    rw [hoN] at hsy
    simp only [psi.injEq] at hsy
    rw [← hsy.2.1] at ht
    exact T.not_lt_z _ ht.1
  · refine ⟨Lc, R, y, hCLM, hv, hLm.symm, by rw [← hoc]; exact hsy, le_refl _, ?_⟩
    rw [← hv, ← hLm]
    exact ht

/-- `rw_frame_of_shapeX` for the widened fifth frame shape. -/
theorem rw_frame_of_shapeXU {M N : Mat} {ρ σ : Valn} {k : Nat}
    (hC : Cons M ρ) (hCN : Cons N σ) (hS : FrameShapeXU M N ρ σ k)
    {Lc : List Nat} {c : Nat} {R : List Nat} (hCL : CL N k = Lc ++ c :: R)
    {s y : T} (hc : σ.o c = psi s y z)
    (ht : lt (spArg (σ.v k) z (sumN (Lc.map σ.o))) y = true ∧
      lt (psi (σ.v k) z z) (psi s y z) = true) :
    ∃ y', CL M k = Lc ++ c :: R ∧ ρ.v k = σ.v k ∧ Lc.map ρ.o = Lc.map σ.o ∧
      ρ.o c = psi s y' z ∧
      (lt (spArg (ρ.v k) z (sumN (Lc.map ρ.o))) y' = true ∧
        lt (psi (ρ.v k) z z) (psi s y' z) = true) := by
  rcases hS with hS | ⟨hv, Lc0, c0, V, hclM, hclN, hsame, hoN, hoM, hVl, hOl, hsm, hoi⟩
  · exact rw_frame_of_shapeX hC hCN hS hCL hc ht
  rcases shape4_split hclM hclN hsame hCL with ⟨-, -, rfl⟩ | ⟨hCLM, hLm, hoc⟩
  · exfalso
    rw [hoN] at hc
    simp only [psi.injEq] at hc
    rw [← hc.2.1] at ht
    exact T.not_lt_z _ ht.1
  · refine ⟨y, hCLM, hv.symm, hLm.symm, by rw [← hoc]; exact hc, ?_⟩
    rw [← hv, ← hLm]
    exact ht

/-- `clField_of_shapeSX` when the fifth case has a foreign allowance. -/
theorem clField_of_shapeSXU {Q : T → List T → T → Prop}
    (hQlow : ∀ a Lv cv cv', Q a Lv cv → Lhd z cv' cv → isOT cv' = true →
      (∃ s y, cv = psi s y z) →
      (∀ s y s' y', cv = psi s y z → cv' = psi s' y' z → s' ≠ s → y' = z) → Q a Lv cv')
    (hQlowV : ∀ a Lv s s', Q a Lv (psi s z z) → Lhd a (psi s' z z) (psi s z z) →
      isOT (psi s' z z) = true → Q a Lv (psi s' z z))
    (hQlowVG : ∀ (V : T) a Lv s s', Q a Lv (psi s z z) → Lhd V (psi s' z z) (psi s z z) →
      (∀ u, ∀ g ∈ comps u V, g < psi s' z z) → isOT (psi s' z z) = true → Q a Lv (psi s' z z))
    {M N : Mat} {ρ σ : Valn} {i : Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hCN : Cons N σ) (hGN : Good3 N σ) (hS : FrameShapeXU M N ρ σ i)
    (hQ : ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R →
      Q (ρ.v i) (Lc.map ρ.o) (ρ.o c)) :
    ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL N i = Lc ++ c :: R →
      Q (σ.v i) (Lc.map σ.o) (σ.o c) := by
  rcases hS with hS | ⟨hv, Lc0, c0, V, hclM, hclN, hsame, hoN, hoM, hVl, hOl, hsm, hoi⟩
  · exact clField_of_shapeSX hQlow hQlowV hC hG hCN hGN hS hQ
  intro Lc c R hCL
  rcases shape4_split hclM hclN hsame hCL with ⟨rfl, rfl, rfl⟩ | ⟨hCLM, hLm, hoc⟩
  · have hq := hQ Lc c [] hclM
    rw [hoM] at hq
    have hcN : c < N.length :=
      (mem_children (cl_mem_children (show c ∈ CL N i by rw [hclN]; simp))).2
    have hot := hGN.ot_o c hcN
    rw [hoN] at hot ⊢
    rw [hv, List.map_congr_left hsame]
    rw [hoN, hoM] at hOl
    have hsm' : ∀ u, ∀ g ∈ comps u V, g < psi (σ.v c) z z := by
      simpa only [hoN] using hsm
    exact hQlowVG V _ _ _ _ hq hOl hsm' hot
  · rw [hv, hLm, hoc]
    exact hQ Lc c R hCLM

end Ytosk.WfT2X
