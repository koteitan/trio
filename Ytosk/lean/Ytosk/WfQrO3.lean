/-
**WfQrO3 (2026-11-01): the base clause `hB` of `OmSide1` when the low part is empty.**
For a single `Y = ψ_a(b) ≥ ε₀` with `lo(b) = 0`, `ω^Y = Y` (`omega_self`).  If also `Y_N = fsD(Y, η) = ψ_a(b_N)` is
standard, `≥ ε₀` and `lo(b_N) = 0` (the first half of `hLo`, `WfQrO2.lo_keep`), then `fsD(ω^Y) = ω^{fsD Y}` and
`fsD(ω^Y) < ω^Y` (`hB_lo0`).  The case `lo(b) ≠ 0` (`ω^Y = ψ_a(hi(b) + Y)`) stays a field.
-/
import Ytosk.WfQrO2

namespace Ytosk.WfQrO3
open T Ytosk Ytosk.WfQrL1 Ytosk.WfQrL2 Ytosk.WfQrL13 Ytosk.WfQrH4 Ytosk.WfQrO1 Ytosk.WfQrO2

/-- `ω^Y = Y` for a single standard `Y = ψ_a(b) ≥ ε₀` without low part. -/
theorem omega_self {a b : T} (hx : isOT (psi a b z) = true) (h : ¬ psi a b z < E0) (hlo : loOf a b = z) :
    omega (psi a b z) = psi a b z := by
  rw [omega_big' hx h, if_pos hlo, app_z_right]
  have e := split_app (psi (succ a) z z) b
  unfold loOf at hlo
  rw [hlo, app_z_right] at e
  unfold hiOf
  rw [e]

/-- **`hB` when the low part is empty** (both sides). -/
theorem hB_lo0 {η a b bN : T} (hx : isOT (psi a b z) = true) (h : ¬ psi a b z < E0) (hlo : loOf a b = z)
    (hxN : isOT (psi a bN z) = true) (hN : ¬ psi a bN z < E0) (hloN : loOf a bN = z)
    (hlt : psi a bN z < psi a b z) :
    psi a bN z = fsD (psi a b z) η →
      fsD (omega (psi a b z)) η = omega (fsD (psi a b z) η) ∧ fsD (omega (psi a b z)) η < omega (psi a b z) := by
  intro hYN
  rw [omega_self hx h hlo, ← hYN, omega_self hxN hN hloN]
  exact ⟨rfl, hlt⟩

/-- **PreB is a special case of PreG**: `pre ≤ init(y)` and any witness `lc` of the last summand give `PreG`. -/
theorem preG_of_preB {η B l lN lc Q s y pre : T} (hl : l = psi s y z) (hG : DQG η false l lN lc)
    (hQ : ∀ q ∈ summands Q, lN ≤ q ∧ q < l) (hp : pre ≤ B) :
    ∃ yc, DQG η true (app B l) (app B (app Q lN)) yc ∧ pre ≤ yc :=
  ⟨app B lc, DQG.mk hl hG hQ, le_trans hp (le_app_self B lc)⟩

end Ytosk.WfQrO3
