/-
**WfQrH8 (2026-11-01): the upgrade step `hUpgL` from the single last summand.**
`v(k) = B ++ l`, `v_N(k) = B ++ Q ++ l_N` (the single-last decomposition of `DQ η true`): if `l_N` is single, then
`last v_N(k) = l_N` and `DQ η false (last v(k)) (last v_N(k))` (`DQ.last1`, stated for the single-last decomposition
only, unlike WfQrL12.DQ.last).  `upgL_of`: the three conjuncts of `hUpgL` from standard `v(k)`, `v_N(k)` and this field.
-/
import Ytosk.WfQrL12
import Ytosk.V3ExpT1
import Ytosk.V3ValT1R

namespace Ytosk.WfQrH8
open T Ytosk Ytosk.WfQrL2 Ytosk.WfQrL12

/-- **The last summands of a `DQ` sum** (single-last decomposition). -/
theorem DQ.last1 {η t tN : T} (h : DQ η true t tN)
    (hs : ∀ B l lN Q, t = app B l → (∃ s0 y0, l = psi s0 y0 z) → tN = app B (app Q lN) → DQ η false l lN →
      ∃ s y, lN = psi s y z) :
    DQ η false (last t) (last tN) := by
  obtain ⟨B, l, lN, Q, s, y, et, etN, hl, hd, _⟩ := DQ.true_inv h
  obtain ⟨s', y', hlN⟩ := hs B l lN Q et ⟨s, y, hl⟩ etN hd
  subst et etN hl hlN
  rw [last_app_single, ← app_assoc, last_app_single]
  exact hd

/-- **`hUpgL` at one upgrade frame.** -/
theorem upgL_of {t tN : T} (ht : isOT t = true) (htz : t ≠ z) (htN : isOT tN = true) (htNz : tN ≠ z)
    (hs : ∀ η, DQ η true t tN → ∀ B l lN Q, t = app B l → (∃ s0 y0, l = psi s0 y0 z) →
      tN = app B (app Q lN) → DQ η false l lN → ∃ s y, lN = psi s y z) :
    Single (last t) ∧ Single (last tN) ∧ ∀ η, DQ η true t tN → DQ η false (last t) (last tN) :=
  ⟨⟨isOT_last ht, last_single' htz⟩, ⟨isOT_last htN, last_single' htNz⟩, fun η h => DQ.last1 h (hs η h)⟩

end Ytosk.WfQrH8
