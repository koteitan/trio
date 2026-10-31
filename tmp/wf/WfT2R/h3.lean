/-
**WfT2R3: the remaining consumers of `T2BelowXResAt` with `T2BelowXResAtX` (2026-11-01).**

Copies (suffix `XR`) of `bumpFields_expand_t2` (V3ExpT2BD), `hR2_t2`・`hR2_t2_ofW` (V3T2R2・V3T2R3),
`rootP_expand_t2` (V3ExpT2RP), `G.ph3c_expand_t2(S)`・`G.fc3_expand_t2(S)` (V3PT2G・V3PSeedAllG),
`t2_val_expand`・`hExp_t2_inv3V2` (V3ExpT2Inv2), `expT2V2_of`・`r2V2_of` (V3ExpT2V2), `vsmallF_expand_t2(V)`
(V3T2VSF), `clField_expand_t2SK` (V3RwClCopy), `frameClosed_expand_t2K`・`t2VSFCV2_of` (V3T2VSFC),
`t2VSFCV2_of2` (V3T2SeedFrV2).
-/
import Ytosk.WfT2R2
import Ytosk.V3ExpT2BD
import Ytosk.V3T2R3
import Ytosk.V3ExpT2RP
import Ytosk.V3PSeedAllG
import Ytosk.V3ExpT2Inv2
import Ytosk.V3ExpT2V2
import Ytosk.V3T2VSF
import Ytosk.V3RwClCopy
import Ytosk.V3T2VSFC
import Ytosk.V3T2SeedFrV2

namespace Ytosk.G

open T

/-- `hQlowV` for `QT2F`: an argument-free last child does not rewrite, and `QFO` does not read it. -/
theorem qT2F_lowVXR : ∀ a Lv s s', QT2F a Lv (psi s z z) → Lhd a (psi s' z z) (psi s z z) →
    isOT (psi s' z z) = true → QT2F a Lv (psi s' z z) := by
  intro a Lv s s' h hl hot
  refine ⟨WfT2X.qFO_lowV a Lv s s' h.1 hl hot, ?_⟩
  intro s0 y0 c0 hc ht
  simp only [psi.injEq] at hc
  rw [← hc.2.1] at ht; exact absurd ht.1 (T.not_lt_z _)

/-- `hQlowV` for `QT2P`. -/
theorem qT2P_lowVXR : ∀ a Lv s s', QT2P a Lv (psi s z z) → Lhd a (psi s' z z) (psi s z z) →
    isOT (psi s' z z) = true → QT2P a Lv (psi s' z z) := by
  intro a Lv s s' h hl hot
  refine ⟨WfT2X.qFO_lowV a Lv s s' h.1 hl hot, ?_⟩
  intro s0 y0 c0 hc ht
  simp only [psi.injEq] at hc
  rw [← hc.2.1] at ht; exact absurd ht.1 (T.not_lt_z _)

end Ytosk.G
