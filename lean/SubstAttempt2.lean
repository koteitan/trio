/-
SubstAttempt2.lean — scratch probe (team-lead task, companion to SubstAttempt).

Isolates obstruction (O2).  In the IDEAL revive subcase — bad root at the front
(r = 0), head a based root `(0,v,z)`, row-1 collapse (srow' = 1) — the tower
machinery `oper_cons_tower1 + tower1_mem` closes EVERYTHING except one goal:

    hgr : ∀ y ∈ W m, based y → graft R' y ∈ Wstar

i.e. the GRAFT CLOSURE for the tail R'.  The revive datum supplies no such
hypothesis; obtaining it is `SubstClosedG`-strength
(`Wtower2.substClosedG_of_subst1g` : `Subst1g → SubstClosedG`), which is
equivalent to the residue itself — so plugging the towers here closes a circle
rather than discharging the core.  (One `sorry`: exactly that graft closure.)
-/
import Wtower2
import Final
import Goper

namespace TRIO
namespace SubstAttempt2

open Wset Three
open Classical

/-- Ideal subcase: `tower1_mem` reduces it to the graft closure `hgr` ALONE. -/
theorem tower1_needs (v z u m : ℕ) (R' : TrioSeq)
    (hR' : argOK R') (hR'ne : R' ≠ [])
    (hd : domT R' m) (hi1 : srow R' (R'.length - 1) = 1)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R') (srow R' (R'.length - 1))
      R'.length)
    (hz1 : z ≤ 1) (hva : 2 * v + z ≤ u) (n : ℕ) :
    (((0, v, z) : ℕ × ℕ × ℕ) :: R')⟦n⟧ ∈ W u := by
  rw [oper_cons_tower1 hR' hR'ne hd hi1 hpM]
  refine tower1_mem hR' hR'ne hz1 hva hd hi1 ?_ hpM n
  -- ⊢ ∀ y ∈ W m, based y → graft R' y ∈ Wstar     (the sole residual = O2)
  trace_state
  sorry

end SubstAttempt2
end TRIO
