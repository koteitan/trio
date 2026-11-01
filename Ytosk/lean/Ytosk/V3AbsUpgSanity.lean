/- Sanity check: the repaired upgrade-shape input accepts the standard
41-column counterexample that refutes the old absorption input. -/
import Ytosk.V3T2AbsXFalse
import Ytosk.V3AbsUpgShape

namespace Ytosk.AbsUpgSanity

open T WfAbsW WfT2X T2AbsXFalse

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

private theorem upg37_unique_fin : ∀ j : Fin 41,
    upg M j.val = some 37 → j.val = 36 := by decide

private theorem no_upg36_fin : ∀ j : Fin 41,
    upg M j.val ≠ some 36 := by decide

private theorem no_bump31_fin : ∀ q : Fin 31,
    par M 0 31 = some q.val → col M 31 ≠ bump M q.val := by decide

private theorem no_bump32_fin : ∀ q : Fin 32,
    par M 0 32 = some q.val → col M 32 ≠ bump M q.val := by decide

/-- The measured upgrade-shape witness uses m = 31, c = 36, p = 32. -/
theorem upg_shape_37 : UpgAbsShape M N ρ σ 37 := by
  unfold UpgAbsShape
  refine ⟨31, 36, 32, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_,
    by decide, by decide, by decide, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hjlt : j < 41
    · exact upg37_unique_fin ⟨j, hjlt⟩ hj
    · have he : entry M 1 j = 0 := by simp [entry, M, Nat.not_lt.mp hjlt]
      simp [upg, he] at hj
  · intro j hj
    by_cases hjlt : j < 41
    · exact no_upg36_fin ⟨j, hjlt⟩ hj
    · have he : entry M 1 j = 0 := by simp [entry, M, Nat.not_lt.mp hjlt]
      simp [upg, he] at hj
  · intro q hq
    have hqLt : q < 31 := par_lt M 0 31 q hq
    exact no_bump31_fin ⟨q, hqLt⟩ hq
  · intro q hq
    have hqLt : q < 32 := par_lt M 0 32 q hq
    exact no_bump32_fin ⟨q, hqLt⟩ hq
  · intro u g hg
    have hall : ∀ g ∈ comps z (ρ.v 31), g < σ.o 36 := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using
        (show (comps z (ρ.v 31)).all (fun g => decide (g < σ.o 36)) = true by decide)
    exact hall g (comps_sub_z u (ρ.v 31) g hg)

/-- The same frame is classified in the repaired bad set `BdXU`. -/
theorem bdXU_37 : BdXU M N ρ σ 40 37 := by
  right
  left
  refine ⟨by decide, by decide, by decide, not_absAt, upg_shape_37⟩

theorem old_absorption_fails_37 : ¬ AbsAt M N ρ σ 37 := not_absAt

end Ytosk.AbsUpgSanity
