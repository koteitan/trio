/-
**The 36-column counterexample of `AbsWN M M[2]` satisfies the bad shape at i = 32 (2026-10-31, WfAbsW).**

`not_absAt`: the absorption `AbsAt` fails at i = 32 (as `WfSrcC3Cex.not_absWN`).
`bad_shape`: `BadAbsShape` holds there (m = 31, no earlier counted child, v(31) unchanged), so the disjunction of
`AbsWNx` takes its second branch at the only failing column (Python: every other bump-type column has `AbsAt`).
-/
import Ytosk.WfSrcC3Cex
import Ytosk.WfAbsWEta
import Ytosk.V3ExpT2BX

namespace Ytosk.WfAbsWCex
open T Ytosk.WfSrcC3Cex Ytosk.WfAbsW
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

theorem not_absAt : ¬ AbsAt M (expand M 2) ρ σ 32 :=
  fun h => s_not_lhd (h s s_mem s_ge2 s_geN s_lt)

theorem bad_shape : BadAbsShape M (expand M 2) ρ σ 32 := by
  refine ⟨31, [], by decide, by decide, by decide, by decide, by decide, by decide, by simp, by decide, ?_⟩
  have key : ∀ j, j < 36 → upg M j ≠ some 32 := by decide
  intro j
  by_cases h : j < 36
  · exact key j h
  · intro hj
    have hl : M.length = 36 := by decide
    have he : entry M 1 j = 0 := entry_out (by omega) 1
    unfold upg at hj
    rw [if_pos (Or.inl he)] at hj
    cases hj

/-- `v(32)` does not go down by `◁` in `M[2]` (u = 0, c = v_M(32)). -/
theorem not_lhd_v : ¬ Lhd z (σ.v 32) (ρ.v 32) := by
  intro h
  have hd := h.2 z (ρ.v 32) h.1 (le_refl _)
  have hno : ¬ ∀ g ∈ comps z (σ.v 32), ∃ y ∈ comps z (ρ.v 32) ++ Gc z z, g ≤ y := by decide
  exact hno hd

/-- `o(32)` does not go down by `◁` in `M[2]` (u = 0, c = o_M(32)). -/
theorem not_lhd_o : ¬ Lhd z (σ.o 32) (ρ.o 32) := by
  intro h
  have hd := h.2 z (ρ.o 32) h.1 (le_refl _)
  have hno : ¬ ∀ g ∈ comps z (σ.o 32), ∃ y ∈ comps z (ρ.o 32) ++ Gc z z, g ≤ y := by decide
  exact hno hd

/-- **The frame shape at m = 31 fails** in `M[2]`: the last counted child 32 changes but not by `◁`. So the
field `FrameShape` of `T2BelowXS` (the conclusion of `t2BelowXS_of`, read by every consumer of `T2BelowXResV2`)
is false here; 31 is not a seed column (`T2SeedCol`: the seed is r = 34 = q). -/
theorem not_frameShape : ¬ FrameShape M (expand M 2) ρ σ 31 := by
  have hclM : CL M 31 = [32] := by decide
  have hclN : CL (expand M 2) 31 = [32] := by decide
  have ho : σ.o 32 ≠ ρ.o 32 := by decide
  rintro (⟨_, _, h⟩ | ⟨_, Lc, c, h1, h2, _, hl, _⟩ | ⟨_, h⟩)
  · exact ho (h 32 (by rw [hclM]; simp))
  · rw [hclM] at h1
    have hc : c = 32 := by
      have := congrArg List.getLast? h1
      simp at this; exact this.symm
    subst hc
    exact not_lhd_o hl
  · rw [hclM] at h; cases h

/-- With the allowance `v(31)`, `v(32)` and `o(32)` do go down (`WfAbsW.bump_col_of_absWNx` derives this from the
bump frame); here we record the value facts that the new design rests on. -/
theorem vm_same : σ.v 31 = ρ.v 31 := by decide

end Ytosk.WfAbsWCex
