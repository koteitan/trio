/-
SubstAttempt.lean — scratch probe (team-lead task): test whether the completed
tower closures (`tower1_mem`, `towerGraft2_holds`) cover the REVIVE case of
`Subst1gRevive`.

RESULT: the revive expansion is

    R⟦n⟧ = R.take r ++ gcopies R r (|R|-1-r) d0 d1 n         (oper_gcopies)

with r = parent R (srow R (|R|-1)) (|R|-1) the BAD ROOT.  The tower lemmas prove
the r = 0, based-head, graft-closed special case only.  Two obstructions:

  (O1) r > 0 in general — the copied block sits AFTER a fixed nonempty prefix
       `R.take r` (revive-by-prefix: the reviving parent lies in `S.take p`
       or in `C`).  `tower1_mem`/`towerGraft2_holds` need the bad root at
       index 0 (`oper_cons_tower1` requires `((0,v,z) :: R')`, parent = 0).
  (O2) graft closure — even at r = 0 they need
       `hgr : ∀ y ∈ W m, based y → graft R' y ∈ Wstar` for the tail R', which
       the revive datum does not supply; getting it is `SubstClosedG`-strength,
       i.e. circular with the residue itself.

`subst1gRevive_of_reviveGcopies` reduces `Subst1gRevive` to the gcopies residual
(GREEN, mechanical via `oper_gcopies`).  `SubstAttempt2.tower1_needs` (a probe
with a single `sorry`) shows the tower lemma, on the best-case subcase, closes
everything except the graft closure (O2).
-/
import Wtower2
import Final
import Goper

namespace TRIO
namespace SubstAttempt

open Wset Three
open Classical

/-- **The residual, as an explicit core.**  Everything in `Subst1gRevive` other
than the shift-copy tower `R.take r ++ gcopies …` is discharged; this names what
survives.  GREEN. -/
def ReviveGcopies : Prop :=
  ∀ (u : ℕ) (R : TrioSeq),
    hasParent R (srow R (R.length - 1)) (R.length - 1) →
    ∀ n : ℕ, 1 ≤ n →
      R.take (parent R (srow R (R.length - 1)) (R.length - 1))
        ++ gcopies R (parent R (srow R (R.length - 1)) (R.length - 1))
            (R.length - 1 - parent R (srow R (R.length - 1)) (R.length - 1))
            (if 0 < srow R (R.length - 1)
              then entry R 0 (R.length - 1)
                - entry R 0 (parent R (srow R (R.length - 1)) (R.length - 1))
              else 0)
            (if 1 < srow R (R.length - 1)
              then entry R 1 (R.length - 1)
                - entry R 1 (parent R (srow R (R.length - 1)) (R.length - 1))
              else 0)
            n ∈ W u

/-- **GREEN reduction**: `ReviveGcopies` (the shift-copy tower with its fixed
prefix) is *exactly* the residue of `Subst1gRevive`. -/
theorem subst1gRevive_of_reviveGcopies (h : ReviveGcopies) : Subst1gRevive := by
  intro u p S C hS hp hCne hCW hhead hdeep hRp hdisj
  set R : TrioSeq := S.take p ++ C ++ S.drop (p + 1) with hRdef
  refine mem_of_oper_mem (fun n hn => ?_)
  have hL : R.length - 1 ≠ 0 := by
    intro hc; rw [hc] at hRp; exact not_hasParent_zero hRp
  have hz : ¬ (entry R 0 (R.length - 1) = 0 ∧ entry R 1 (R.length - 1) = 0 ∧
      entry R 2 (R.length - 1) = 0) := by
    rintro ⟨h0, h1, h2⟩
    have hsr : srow R (R.length - 1) = 0 := by unfold srow; rw [h2]; simp [h1]
    rw [hsr] at hRp
    obtain ⟨j0, hj0, -⟩ := hRp
    simp only [nextR] at hj0
    obtain ⟨-, -, -, hlt, -⟩ := hj0
    rw [h0] at hlt; exact absurd hlt (by omega)
  rw [oper_gcopies n hL hz hRp]
  exact h u R hRp n hn

end SubstAttempt
end TRIO
