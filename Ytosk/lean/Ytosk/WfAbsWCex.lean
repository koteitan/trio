/-
**The 36-column counterexample of `AbsWN M M[2]` satisfies the bad shape at i = 32 (2026-10-31, WfAbsW).**

`not_absAt`: the absorption `AbsAt` fails at i = 32 (as `WfSrcC3Cex.not_absWN`).
`bad_shape`: `BadAbsShape` holds there (m = 31, no earlier counted child, v(31) unchanged), so the disjunction of
`AbsWNx` takes its second branch at the only failing column (Python: every other bump-type column has `AbsAt`).
-/
import Ytosk.WfSrcC3Cex
import Ytosk.WfAbsWEta

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

end Ytosk.WfAbsWCex
