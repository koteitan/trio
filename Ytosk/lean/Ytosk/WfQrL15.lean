/-
**WfQrL15 (2026-11-01): the last-child `o` frame at the parent of the leaf `x`** (`frame_DQ_leafpar`).

Measured (frames.py): at the parent `i` of `x` with `c = x` the last counted child, `o(x) = Ω_{a+1}` (its `fsD` is
the identity on the index), so `M` does not trigger (`y = 0`) and adds: `pre + Ω_{a+1} = B + Ω_{a+1}`.  In `M[n]`
`o_N(x) = ζ = ψ_{s'}(y')` (the chain term) triggers, with a low part: `H(s', y') = hi(y') + ζ`.
If `hi(y') = B + Q` with every summand of `Q` in `[ζ, Ω_{a+1})`, the new value is `ψ_v(B + Q + ζ)`, a `DQ` of
`ψ_v(B + Ω_{a+1})` (base step `Ω_{a+1} → ζ` with the index `ζ`).
-/
import Ytosk.WfQrL14

namespace Ytosk.WfQrL15
open T Ytosk Ytosk.WfQrL2 Ytosk.WfQrL4 Ytosk.WfQrL14

theorem frame_DQ_leafpar {v pre a s' y' B Q : T} (hyN : isOT (psi s' y' z) = true)
    (hnt : ¬ (lt pre z = true ∧ lt (psi v z z) (psi (succ a) z z) = true))
    (htN : lt pre y' = true ∧ lt (psi v z z) (psi s' y' z) = true)
    (hloN : (split y' (psi (succ s') z z)).2 ≠ z)
    (hadd : add pre (psi (succ a) z z) = app B (psi (succ a) z z))
    (hhi : (split y' (psi (succ s') z z)).1 = app B Q)
    (hQ : ∀ q ∈ summands Q, psi s' y' z ≤ q ∧ q < psi (succ a) z z)
    (hlt : psi s' y' z < psi (succ a) z z) :
    ∃ η, DQ η false (psi v (spArg v pre (psi (succ a) z z)) z) (psi v (spArg v pre (psi s' y' z)) z) := by
  rw [spArg_single, spArg_single]
  unfold step
  rw [if_neg hnt, if_pos htN, hadd, H_eq hyN, if_neg hloN, hhi, app_assoc]
  exact ⟨psi s' y' z, DQ.arg (DQ.mk rfl (DQ_om_succ hlt) hQ)⟩

end Ytosk.WfQrL15
