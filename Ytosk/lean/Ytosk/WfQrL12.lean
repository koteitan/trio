/-
**WfQrL12 (2026-11-01): the last summand of a `DQ` sum** (the hypothesis `hUpgL` of `qr_engineDQ`).
`v(i) = B ++ l`, `v_N(i) = B ++ Q ++ l_N`: if the new last summand `l_N` is single, the last summands are related by
the single step `DQ η false l l_N` (`DQ.last`).
-/
import Ytosk.WfQrL11

namespace Ytosk.WfQrL12
open T Ytosk Ytosk.WfQrL2

theorem last_app_single {s y : T} : ∀ B : T, last (app B (psi s y z)) = psi s y z
  | z => rfl
  | psi a b c => by
    simp only [app_psi]
    have ih := last_app_single (s := s) (y := y) c
    cases hc : app c (psi s y z) with
    | z => cases c <;> simp [app] at hc
    | psi a' b' c' => rw [hc] at ih; simpa [last] using ih

/-- **The last summands of a `DQ` sum.** -/
theorem DQ.last {η t tN : T} (h : DQ η true t tN)
    (hs : ∀ B l lN Q, t = app B l → tN = app B (app Q lN) → DQ η false l lN → ∃ s y, lN = psi s y z) :
    DQ η false (last t) (last tN) := by
  obtain ⟨B, l, lN, Q, s, y, et, etN, hl, hd, _⟩ := DQ.true_inv h
  obtain ⟨s', y', hlN⟩ := hs B l lN Q et etN hd
  subst et etN hl hlN
  rw [last_app_single, ← app_assoc, last_app_single]
  exact hd

end Ytosk.WfQrL12
