/-
**WfQrL14 (2026-11-01): two more shapes of the `ω` layer of a bump term** (measured by tmp/wf/WfQrL/frames.py).

* `ε₀` crossing (`omega_DQ_E0`): `Y = ε₀ = ψ_0(Ω_1)` and `Y_N < ε₀` (the bad call of M13: `W = A = ψ(Ω_1)`).
  `ω^{ε₀} = ε₀`, `ω^{Y_N} = ψ_0(Y_N)`, and `Ω_1 → Y_N` is a base step with the index `η' = Y_N`.
* node (`omega_DQ_node`): `Y = ψ_a(B + Ω_{a+1})` (no low part), `Y_N = ψ_a(b_N)` gets a low part with high part
  `B`: `ω^Y = Y`, `ω^{Y_N} = ψ_a(B + Y_N)`, and `Ω_{a+1} → Y_N` is a base step with `η' = Y_N`
  (the `DQ` form of the index lift `omega_lift1/2` of the old engine).
-/
import Ytosk.WfQrL13

namespace Ytosk.WfQrL14
open T Ytosk Ytosk.WfQrL2 Ytosk.WfQrL11

/-- The base step `Ω_{s+1} → Y` with the index `Y`. -/
theorem DQ_om_succ {s Y : T} (h : Y < psi (succ s) z z) : DQ Y false (psi (succ s) z z) Y := by
  have := DQ.base (η := Y) (l := psi (succ s) z z) (by rw [fsD_om_succ]; exact h)
  rwa [fsD_om_succ] at this

/-- **`ε₀` crossing.** -/
theorem omega_DQ_E0 {YN : T} (hYN : YN < E0) (hE : isOT E0 = true) :
    ∃ η, DQ η false (omega E0) (omega YN) := by
  have hfix : omega E0 = E0 := omega_fix_nolo hE (lt_irrefl' _) rfl
  rw [hfix, omega_small hYN]
  have hlt : YN < psi (succ z) z z := by
    refine lt_trans' hYN ?_
    show psi z (psi one z z) z < psi (succ z) z z
    rw [psi_lt_psi_z_iff]; left; exact T.z_lt_psi _ _ _
  refine ⟨YN, ?_⟩
  have hd := DQ.single_true ⟨succ z, z, rfl⟩ (DQ_om_succ hlt)
  exact DQ.arg hd

/-- **Node case of the `ω` layer.** -/
theorem omega_DQ_node {a B bN : T} (hY : isOT (psi a (app B (psi (succ a) z z)) z) = true)
    (hYN : isOT (psi a bN z) = true) (hE : ¬ psi a (app B (psi (succ a) z z)) z < E0)
    (hEN : ¬ psi a bN z < E0)
    (hlo : loOf a (app B (psi (succ a) z z)) = z) (hloN : loOf a bN ≠ z) (hhi : hiOf a bN = B)
    (hlt : psi a bN z < psi (succ a) z z) :
    ∃ η, DQ η false (omega (psi a (app B (psi (succ a) z z)) z)) (omega (psi a bN z)) := by
  rw [omega_fix_nolo hY hE hlo, omega_big' hYN hEN, if_neg hloN, hhi]
  refine ⟨psi a bN z, ?_⟩
  have := DQ.mk (B := B) (Q := z) rfl (DQ_om_succ hlt) (by simp [summands])
  simpa [app] using DQ.arg this

/-- **Trigger in both with a low part in both** (the last `o`-frame shape of frames.py): `H(s, y) = hi(y) + ψ_s(y)`,
`H(s, y_N) = hi(y_N) + ψ_s(y_N)`; with the high part kept (`WfQrL3.hi_keep_DQ`) this is `DQ.arg` under `hi`. -/
theorem frame_DQ_trig_lo {η v pre s y yN : T} (hy : isOT (psi s y z) = true) (hyN : isOT (psi s yN z) = true)
    (hd : DQ η true y yN)
    (ht : lt pre y = true ∧ lt (psi v z z) (psi s y z) = true)
    (htN : lt pre yN = true ∧ lt (psi v z z) (psi s yN z) = true)
    (hlo : (split y (psi (succ s) z z)).2 ≠ z) (hloN : (split yN (psi (succ s) z z)).2 ≠ z)
    (hhi : (split yN (psi (succ s) z z)).1 = (split y (psi (succ s) z z)).1) :
    DQ η false (psi v (spArg v pre (psi s y z)) z) (psi v (spArg v pre (psi s yN z)) z) := by
  rw [WfQrL4.spArg_single, WfQrL4.spArg_single]
  unfold step
  rw [if_pos ht, if_pos htN, H_eq hy, H_eq hyN, if_neg hlo, if_neg hloN, hhi]
  exact DQ.arg (DQ.snoc _ ⟨s, y, rfl⟩ (DQ.arg hd))

end Ytosk.WfQrL14
