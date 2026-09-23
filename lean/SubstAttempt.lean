/-
SubstAttempt.lean — scratch probe (team-lead task): test whether the completed
tower closures (`tower1_mem`, `towerGraft2_holds`) cover the REVIVE case of
`Subst1gRevive`.

Strategy: in the revive configuration, `R = S.take p ++ C ++ S.drop (p+1)` has a
bad root (hypothesis `hRp`).  Reduce `R ∈ W u` to `∀ n, R⟦n⟧ ∈ W u` and unfold
`R⟦n⟧` with `oper_gcopies` to see EXACTLY what shape the tower must match.
-/
import Wtower2
import Final
import Goper

namespace TRIO
namespace SubstAttempt

open Wset Three
open Classical

-- warm-up: toolchain + cache sanity
example : True := trivial

/-- Probe 1: unfold the revive expansion and read off the exact goal. -/
theorem revive_probe : Subst1gRevive := by
  intro u p S C hS hp hCne hCW hhead hdeep hRp hdisj
  set R : TrioSeq := S.take p ++ C ++ S.drop (p + 1) with hRdef
  refine mem_of_oper_mem (fun n hn => ?_)
  -- goal here: R⟦n⟧ ∈ W u
  have hL : R.length - 1 ≠ 0 := by
    intro hc; rw [hc] at hRp; exact not_hasParent_zero hRp
  have hz : ¬ (entry R 0 (R.length - 1) = 0 ∧ entry R 1 (R.length - 1) = 0 ∧
      entry R 2 (R.length - 1) = 0) := by
    rintro ⟨h0, h1, h2⟩
    have hsr : srow R (R.length - 1) = 0 := by unfold srow; rw [h2]; simp [h1]
    rw [hsr] at hRp
    obtain ⟨j0, hj0, -⟩ := hRp
    simp only [nextR, if_pos rfl] at hj0
    obtain ⟨-, -, -, hlt, -⟩ := hj0
    rw [h0] at hlt; exact absurd hlt (by omega)
  rw [oper_gcopies n hL hz hRp]
  trace_state
  sorry

end SubstAttempt
end TRIO
