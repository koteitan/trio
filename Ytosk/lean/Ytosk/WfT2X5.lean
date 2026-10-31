/-
**WfT2X5: the frame-shape readers with the fourth case (2026-11-01, t = 2 Bad2 route).**

The fourth case of `FrameShapeX` (WfAbsWFrame): `v(i)` unchanged, `CL_M i = CL_N i = Lc ++ [c]`, the `o` of `Lc`
unchanged, `c` argument-free in `M` and `N` and lowered with the allowance `v(i)` only.
`shape4_split`: a frame of `N` at `i` either ends at `c` (then it does not rewrite: the argument is `0`), or it is a
frame of `M` with the same values.
- `frame_of_shapeX` (V3T2VRAPre `frame_of_shape`), `rw_frame_of_shapeX` (V3T2VRASeed `rw_frame_of_shape`):
  rewriting frames — the fourth case is free.
- `clField_of_shapeX` (V3ExpT2FO `clField_of_shape`), `clField_of_shapeSX` (V3T2VSR `clField_of_shapeS`): value
  fields of frames — the fourth case needs `hQlowV` (the field survives lowering an argument-free last child by
  `◁_a`, `a` the frame's own `v`) and the standard form of the new child.
-/
import Ytosk.WfT2X4
import Ytosk.V3T2VRAPre
import Ytosk.V3T2VRASeed

namespace Ytosk.WfT2X

open T Classical Ytosk.WfAbsW

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **A frame of `N` in the fourth case**: it ends at the bad child, or it is a frame of `M` with the same values. -/
theorem shape4_split {M N : Mat} {ρ σ : Valn} {i c0 : Nat} {Lc0 : List Nat}
    (hclM : CL M i = Lc0 ++ [c0]) (hclN : CL N i = Lc0 ++ [c0]) (hsame : ∀ d ∈ Lc0, σ.o d = ρ.o d)
    {Lc : List Nat} {c : Nat} {R : List Nat} (hCL : CL N i = Lc ++ c :: R) :
    (R = [] ∧ Lc = Lc0 ∧ c = c0) ∨
      (CL M i = Lc ++ c :: R ∧ Lc.map σ.o = Lc.map ρ.o ∧ σ.o c = ρ.o c) := by
  by_cases hR : R = []
  · subst hR
    rw [hclN] at hCL
    obtain ⟨h1, h2⟩ := List.append_inj' hCL rfl
    simp only [List.cons.injEq, and_true] at h2
    exact Or.inl ⟨rfl, h1.symm, h2.symm⟩
  · right
    have hCLM : CL M i = Lc ++ c :: R := by rw [hclM, ← hclN, hCL]
    have hdl : (Lc ++ c :: R).dropLast = Lc0 := by rw [← hCL, hclN]; simp
    rw [List.dropLast_append_of_ne_nil (by simp)] at hdl
    have hLs : ∀ d ∈ Lc, d ∈ Lc0 := fun d hd => by rw [← hdl]; exact List.mem_append_left _ hd
    have hcs : c ∈ Lc0 := by
      rw [← hdl]
      apply List.mem_append_right
      obtain ⟨r0, rs, rfl⟩ := List.exists_cons_of_ne_nil hR
      simp
    exact ⟨hCLM, List.map_congr_left (fun d hd => hsame d (hLs d hd)), hsame c hcs⟩

/-- **`frame_of_shape` (V3T2VRAPre) with `FrameShapeX`.** -/
theorem frame_of_shapeX {M N : Mat} {ρ σ : Valn} {i : Nat} (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ)
    (hGN : Good3 N σ) (hS : FrameShapeX M N ρ σ i) {Lc : List Nat} {c : Nat} {R : List Nat}
    (hCL : CL N i = Lc ++ c :: R) {s y : T} (hsy : σ.o c = psi s y z)
    (ht : lt (spArg (σ.v i) z (sumN (Lc.map σ.o))) y = true ∧ lt (psi (σ.v i) z z) (psi s y z) = true) :
    ∃ (Lc' R' : List Nat) (yM : T), CL M i = Lc' ++ c :: R' ∧ σ.v i = ρ.v i ∧ Lc'.map ρ.o = Lc.map σ.o ∧
      ρ.o c = psi s yM z ∧ y ≤ yM ∧
      (lt (spArg (ρ.v i) z (sumN (Lc'.map ρ.o))) yM = true ∧ lt (psi (ρ.v i) z z) (psi s yM z) = true) := by
  rcases hS with hS | ⟨hv, Lc0, c0, hclM, hclN, hsame, hoN, hoM, hVl, hOl, hoi⟩
  · exact frame_of_shape hC hG hCN hGN hS hCL hsy ht
  rcases shape4_split hclM hclN hsame hCL with ⟨-, -, rfl⟩ | ⟨hCLM, hLm, hoc⟩
  · exfalso
    rw [hoN] at hsy; simp only [psi.injEq] at hsy
    rw [← hsy.2.1] at ht; exact T.not_lt_z _ ht.1
  · refine ⟨Lc, R, y, hCLM, hv, hLm.symm, by rw [← hoc]; exact hsy, le_refl _, ?_⟩
    rw [← hv, ← hLm]; exact ht

/-- **`rw_frame_of_shape` (V3T2VRASeed) with `FrameShapeX`.** -/
theorem rw_frame_of_shapeX {M N : Mat} {ρ σ : Valn} {k : Nat} (hC : Cons M ρ) (hCN : Cons N σ)
    (hS : FrameShapeX M N ρ σ k) {Lc : List Nat} {c : Nat} {R : List Nat} (hCL : CL N k = Lc ++ c :: R)
    {s y : T} (hc : σ.o c = psi s y z)
    (ht : lt (spArg (σ.v k) z (sumN (Lc.map σ.o))) y = true ∧ lt (psi (σ.v k) z z) (psi s y z) = true) :
    ∃ y', CL M k = Lc ++ c :: R ∧ ρ.v k = σ.v k ∧ Lc.map ρ.o = Lc.map σ.o ∧ ρ.o c = psi s y' z ∧
      (lt (spArg (ρ.v k) z (sumN (Lc.map ρ.o))) y' = true ∧ lt (psi (ρ.v k) z z) (psi s y' z) = true) := by
  rcases hS with hS | ⟨hv, Lc0, c0, hclM, hclN, hsame, hoN, hoM, hVl, hOl, hoi⟩
  · exact rw_frame_of_shape hC hCN hS hCL hc ht
  rcases shape4_split hclM hclN hsame hCL with ⟨-, -, rfl⟩ | ⟨hCLM, hLm, hoc⟩
  · exfalso
    rw [hoN] at hc; simp only [psi.injEq] at hc
    rw [← hc.2.1] at ht; exact T.not_lt_z _ ht.1
  · refine ⟨y, hCLM, hv.symm, hLm.symm, by rw [← hoc]; exact hc, ?_⟩
    rw [← hv, ← hLm]; exact ht

/-- **`clField_of_shape` (V3ExpT2FO) with `FrameShapeX`**: the fourth case needs `hQlowV`. -/
theorem clField_of_shapeX {Q : T → List T → T → Prop}
    (hQlow : ∀ a Lv cv cv', Q a Lv cv → Lhd z cv' cv → isOT cv' = true → Q a Lv cv')
    (hQlowV : ∀ a Lv s s', Q a Lv (psi s z z) → Lhd a (psi s' z z) (psi s z z) → isOT (psi s' z z) = true →
      Q a Lv (psi s' z z))
    {M N : Mat} {ρ σ : Valn} {i : Nat} (hS : FrameShapeX M N ρ σ i)
    (hOT : ∀ d ∈ CL N i, isOT (σ.o d) = true)
    (hQ : ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R → Q (ρ.v i) (Lc.map ρ.o) (ρ.o c)) :
    ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL N i = Lc ++ c :: R → Q (σ.v i) (Lc.map σ.o) (σ.o c) := by
  rcases hS with hS | ⟨hv, Lc0, c0, hclM, hclN, hsame, hoN, hoM, hVl, hOl, hoi⟩
  · exact clField_of_shape hQlow hS hQ
  intro Lc c R hCL
  have hcN : c ∈ CL N i := by rw [hCL]; simp
  rcases shape4_split hclM hclN hsame hCL with ⟨rfl, rfl, rfl⟩ | ⟨hCLM, hLm, hoc⟩
  · have hq := hQ Lc c [] hclM
    rw [hoM] at hq
    have hot := hOT c hcN
    rw [hoN] at hot ⊢
    rw [hv, List.map_congr_left hsame]
    rw [hoN, hoM] at hOl
    exact hQlowV _ _ _ _ hq hOl hot
  · rw [hv, hLm, hoc]; exact hQ Lc c R hCLM

/-- **`clField_of_shapeS` (V3T2VSR) with `FrameShapeX`**: the fourth case needs `hQlowV`. -/
theorem clField_of_shapeSX {Q : T → List T → T → Prop}
    (hQlow : ∀ a Lv cv cv', Q a Lv cv → Lhd z cv' cv → isOT cv' = true → (∃ s y, cv = psi s y z) →
      (∀ s y s' y', cv = psi s y z → cv' = psi s' y' z → s' ≠ s → y' = z) → Q a Lv cv')
    (hQlowV : ∀ a Lv s s', Q a Lv (psi s z z) → Lhd a (psi s' z z) (psi s z z) → isOT (psi s' z z) = true →
      Q a Lv (psi s' z z))
    {M N : Mat} {ρ σ : Valn} {i : Nat} (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hGN : Good3 N σ)
    (hS : FrameShapeX M N ρ σ i)
    (hQ : ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R → Q (ρ.v i) (Lc.map ρ.o) (ρ.o c)) :
    ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL N i = Lc ++ c :: R → Q (σ.v i) (Lc.map σ.o) (σ.o c) := by
  rcases hS with hS | ⟨hv, Lc0, c0, hclM, hclN, hsame, hoN, hoM, hVl, hOl, hoi⟩
  · exact clField_of_shapeS hQlow hC hG hCN hGN hS hQ
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
    exact hQlowV _ _ _ _ hq hOl hot
  · rw [hv, hLm, hoc]; exact hQ Lc c R hCLM

end Ytosk.WfT2X
