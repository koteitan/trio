/-
**WfQrL11 (2026-11-01): the node case of the last-child `o` frame.**

Measured (tmp/wf/WfQrL/frames.py, notes): the trigger agreement `hTrig` of `qr_engineDQ` fails, yet the new
`o(i)` is still a `DQ` of the old one.  One failing shape: the trigger fires in `M` and in `M[n]`,
`y = B + Ω_{s+1}` has no low part, and `y_N` has one (`Ω_{s+1}` is replaced by something below it).
Then `H(s, y) = y` and `H(s, y_N) = B + ψ_s(y_N)`, and `Ω_{s+1} → ψ_s(y_N)` is a base step of `fsD` with the
index `η = ψ_s(y_N)` (`fsD(Ω_{s+1}, η) = η`): `frame_DQ_node`.
-/
import Ytosk.WfQrL10

namespace Ytosk.WfQrL11
open T Ytosk Ytosk.WfQrL2 Ytosk.WfQrL4

/-- `fsD(Ω_{s+1}, η) = η`. -/
theorem fsD_om_succ (s η : T) : fsD (psi (succ s) z z) η = η := by
  unfold fsD
  rw [if_pos rfl, if_neg (succ_ne_z s), if_pos (isSucc_succ s)]

/-- **The node case**: trigger in both, `y = B + Ω_{s+1}` without a low part, `y_N` with a low part and high part
`B`, and `ψ_s(y_N) < Ω_{s+1}`. -/
theorem frame_DQ_node {v pre s y yN B : T} (hy : isOT (psi s y z) = true) (hyN : isOT (psi s yN z) = true)
    (ht : lt pre y = true ∧ lt (psi v z z) (psi s y z) = true)
    (htN : lt pre yN = true ∧ lt (psi v z z) (psi s yN z) = true)
    (hlo : (split y (psi (succ s) z z)).2 = z) (hloN : (split yN (psi (succ s) z z)).2 ≠ z)
    (hyB : y = app B (psi (succ s) z z)) (hhi : (split yN (psi (succ s) z z)).1 = B)
    (hlt : psi s yN z < psi (succ s) z z) :
    ∃ η, DQ η false (psi v (spArg v pre (psi s y z)) z) (psi v (spArg v pre (psi s yN z)) z) := by
  refine ⟨psi s yN z, ?_⟩
  rw [spArg_single, spArg_single]
  unfold step
  rw [if_pos ht, if_pos htN, H_nolo hy hlo, H_eq hyN, if_neg hloN, hhi, hyB]
  have hb : DQ (psi s yN z) false (psi (succ s) z z) (psi s yN z) := by
    have := DQ.base (η := psi s yN z) (l := psi (succ s) z z) (by rw [fsD_om_succ]; exact hlt)
    rwa [fsD_om_succ] at this
  have := DQ.mk (B := B) (Q := z) rfl hb (by simp [summands])
  simpa [app] using DQ.arg this

end Ytosk.WfQrL11
