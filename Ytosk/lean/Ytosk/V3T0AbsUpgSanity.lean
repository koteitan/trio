/- Sanity check for the t=0 upgrade-aware bad-column input on its 39-column counterexample. -/
import Ytosk.V3T0AbsFalse
import Ytosk.V3AbsUpgShape

namespace Ytosk.T0AbsUpgSanity

open T WfAbsW WfT2X Ytosk.T0AbsFalse

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-- At the failing t=0 column 34, the ordinary absorption clause is false. -/
theorem not_absAt_34 : ¬ AbsAt M N ρ σ 34 := by
  intro h
  have hq : q ∈ summands (vOpt ρ (par M 1 34)) := by decide
  exact not_lhd (h q hq (by decide) (by decide) (by decide))

/-- The frame is covered by the old bad shape and hence by the widened bad set. -/
theorem bad_shape_34 : BadAbsShape M N ρ σ 34 := bad_shape

theorem bdXU_34 : BdXU M N ρ σ 37 34 := by
  left
  exact ⟨by decide, by decide, by decide, not_absAt_34, bad_shape_34⟩

/-- The new local input takes the BadAbsShape branch at this column. -/
theorem AbsWNxU_branch_34 :
    AbsAt M N ρ σ 34 ∨ BadAbsShape M N ρ σ 34 ∨ UpgAbsShape M N ρ σ 34 :=
  Or.inr (Or.inl bad_shape_34)

end Ytosk.T0AbsUpgSanity
