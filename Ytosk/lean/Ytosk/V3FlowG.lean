/-
**The flow with a general source (2026-11-08): helpers.**

The helpers of V3SVFlowM with the weaker hypothesis on `x − 1`: `upg M (x − 1)` is `none` or `some x`
(`hux : ∀ c, upg M (x − 1) = some c → c = x`). This covers the sv case (`upg(x − 1) = x`) and the C1 case
(`upg(x − 1) = none`).
-/
import Ytosk.V3SVStrictTop

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section
variable {M : Mat} {x r : Nat} (hx : x + 1 = M.length) (hxr : par M 0 x = some r)
include hx hxr

/-- Only `r` has `x` as a child. -/
theorem x_child_eqG {w : Nat} (h : x ∈ children M w) : w = r := by
  have := (mem_children_iff.mp h).2; rw [hxr] at this; exact (Option.some.inj this).symm

theorem child_lt_xG {w c : Nat} (hwr : w ≠ r) (hc : c ∈ children M w) : c < x := by
  have hcM := (mem_children hc).2
  by_contra h
  have : c = x := by omega
  subst this
  exact hwr (x_child_eqG hx hxr hc)

/-- Countedness is the same in `M.take x` below `r`. -/
theorem cnt_eqNG (hux : ∀ c, upg M (x - 1) = some c → c = x) {w j : Nat} (hw : w < x) (hj : j < x)
    (hjr : j ≠ r) : (Counted (M.take x) w j ↔ Counted M w j) := by
  by_contra h
  rcases cnt_change hx hw hj h with hxc | hu
  · exact hjr (x_child_eqG hx hxr hxc)
  · have := hux j hu; omega

/-- **An uncounted non-bump child** is an upgrade target and topped. -/
theorem u_nodeG {w j : Nat} (hjx : j < x) (hjr : j ≠ r) (hb : col M j ≠ bump M w)
    (hnc : ¬ Counted (M.take x) w j) (hw : w < x) :
    (∃ i, i + 1 < x ∧ upg M i = some j) ∧ topped M j = true := by
  have h : isUpg (M.take x) j = true ∧ topped (M.take x) j = true := by
    by_contra hn
    apply hnc
    exact ⟨by rw [col_take M hjx, bump_take M hw]; exact hb, hn⟩
  have hxj : x ∉ children M j := fun h' => hjr (x_child_eqG hx hxr h')
  exact ⟨(isUpg_take M (by omega) j).mp h.1, by rw [← topped_take_eq hx hjx hxj]; exact h.2⟩

end

end Ytosk.V3Main.SeedPF
