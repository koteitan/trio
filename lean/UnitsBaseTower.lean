/-
UnitsBaseTower.lean — units_base = GTC CQ v ([(1,v+1,1)]ⁿ) via oper_zcone on the last
(2,u+1,1), generalizing GTC_far_CQ (HbB:170) from 1 to n far-heads.
The word rcol's to (0,u,0)::(QB++farW)++(1,u+1,1)::[(2,u+1,1)]ⁿ; last (2,u+1,1) = zcone.
-/
import HbB
import GzD

namespace TRIO
namespace UnitsBaseTower

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GzD GzH GzJ HbB

/-- units_base: n-far-head word in CQ. Probe the goal after GTC unfold + rcol. -/
theorem units_base (v : ℕ) : ∀ n,
    GTC CQ v ((List.range n).flatMap (fun _ => [((1, v + 1, 1) : ℕ × ℕ × ℕ)])) := by
  intro n
  intro L hC hL hB u hu _ a ha
  obtain ⟨bs, uss, hR, hNT, rfl⟩ := hC
  trace_state
  sorry

end UnitsBaseTower
end TRIO
