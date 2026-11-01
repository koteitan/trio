/-
**V3AbsUpgFrame (2026-11-02): the frame shape with a foreign allowance.**

`WfAbsW.FrameShapeX` has a fourth case where the last counted child `c` of `i` goes down with the allowance `v(i)`.
At the parent `p = P₀ c` of an upgrader of an upgrade-shape bad column (V3AbsUpgShape), `c` goes down only with the
allowance `V = v(P₁ c) ≠ v(p)` (`Lhd_{v(p)}` fails in 4 of the 6 measured frames), but every component of `V` is below
the new `o(c)`.

- `FrameShape5`: the fifth case (any allowance `V` whose components lie below the new `o(c)`).
- `FrameShapeXU := FrameShapeX ∨ FrameShape5`; `FrameShapeX.toU`.
- `vs_changed_boundVG`: `WfT2X.vs_changed_boundV` with the allowance `V` in place of the level `a`; the only reader
  of the fourth case that uses its `Lhd` (`qVSF_of_shapeX`, WfT2X6).  The other readers (`clField_of_shapeX` with
  `QFC`・`QFCo`・`QVRAt`・`QFO`, `frame_of_shapeX`, `rw_frame_of_shapeX`, `pathLv_of_shapeXR`) do not use it.
-/
import Ytosk.WfT2X6

namespace Ytosk.WfAbsW

open T

set_option linter.unusedVariables false

/-- **The fifth frame case**: as the fourth case of `FrameShapeX`, with any allowance `V` whose components (at every
level) lie below the new `o(c)`. -/
def FrameShape5 (M N : Mat) (ρ σ : Valn) (i : Nat) : Prop :=
  σ.v i = ρ.v i ∧ ∃ Lc c V, CL M i = Lc ++ [c] ∧ CL N i = Lc ++ [c] ∧ (∀ d ∈ Lc, σ.o d = ρ.o d) ∧
    σ.o c = psi (σ.v c) z z ∧ ρ.o c = psi (ρ.v c) z z ∧
    Lhd V (σ.v c) (ρ.v c) ∧ Lhd V (σ.o c) (ρ.o c) ∧ (∀ u, ∀ g ∈ comps u V, g < σ.o c) ∧
    Lhd z (σ.o i) (ρ.o i)

/-- **The frame shape with the foreign-allowance case.** -/
def FrameShapeXU (M N : Mat) (ρ σ : Valn) (i : Nat) : Prop :=
  FrameShapeX M N ρ σ i ∨ FrameShape5 M N ρ σ i

theorem FrameShapeX.toU {M N : Mat} {ρ σ : Valn} {i : Nat} (h : FrameShapeX M N ρ σ i) :
    FrameShapeXU M N ρ σ i := Or.inl h

end Ytosk.WfAbsW

namespace Ytosk.WfT2X

open T Ytosk.WfAbsW

set_option linter.unusedVariables false

/-- **`vs_changed_boundV` with a foreign allowance** whose components at level `a` lie below `ψ_{s'}(0)`. -/
theorem vs_changed_boundVG {a V B s s' : T} (ha : isOT a = true) (hs'ot : isOT s' = true) (hl : Lhd V s' s)
    (hsm : ∀ g ∈ comps a V, g < psi s' z z)
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
        (fun _ g hg => hsm g hg)
    by_cases hsa : s' < a
    · rw [comps_nil_of_lt hs'ot hsa] at hg; simp at hg
    · have hall := ((isOT_psi_iff).mp hot').2.2.2.2
      left
      apply le_of_lt
      apply hall g
      rw [comps_psi_z_of_ge hsa]
      simp [hg]
  · obtain ⟨d, hd, hgd⟩ := hl.2 a s hl.1 (le_refl s) g hg
    rcases List.mem_append.mp hd with hd | hd
    · right
      rcases hsub d hd with h | h
      · exact le_trans hgd (le_trans h (le_of_summands_ge hB hBc))
      · exact le_trans hgd h
    · simp only [Gc, List.mem_cons] at hd
      rcases hd with rfl | hd
      · right; exact le_trans hgd (z_le _)
      · left; exact le_of_lt (lt_of_le_of_lt hgd (hsm d hd))

end Ytosk.WfT2X
