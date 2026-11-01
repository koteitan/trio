/-
The low-value field lemmas used by widened frame readers.  The fifth frame
case carries a component bound, but these fields do not inspect that bound.
-/
import Ytosk.WfT2X6U
import Ytosk.V3T2FC
import Ytosk.V3T2VRA

namespace Ytosk.WfT2X

open T Classical Ytosk.WfAbsW

set_option linter.unusedVariables false

theorem qFC_lowVG : ∀ (V : T) a Lv s s', QFC a Lv (psi s z z) →
    Lhd V (psi s' z z) (psi s z z) →
    (∀ u, ∀ g ∈ comps u V, g < psi s' z z) → isOT (psi s' z z) = true →
    QFC a Lv (psi s' z z) := by
  intro V a Lv s s' _ _ _ _ s0 y0 h ht
  simp only [psi.injEq] at h
  rw [← h.2.1] at ht
  exact absurd ht.1 (T.not_lt_z _)

theorem qFCo_lowVG : ∀ (V : T) a Lv s s', QFCo a Lv (psi s z z) →
    Lhd V (psi s' z z) (psi s z z) →
    (∀ u, ∀ g ∈ comps u V, g < psi s' z z) → isOT (psi s' z z) = true →
    QFCo a Lv (psi s' z z) := by
  intro V a Lv s s' h hl hsm hot
  exact ⟨hot, qFC_lowVG V a Lv s s' h.2 hl hsm hot⟩

theorem qVRAt_lowVG (u : T) : ∀ (V : T) a Lv s s', QVRAt a Lv (psi s z z) u →
    Lhd V (psi s' z z) (psi s z z) →
    (∀ u, ∀ g ∈ comps u V, g < psi s' z z) → isOT (psi s' z z) = true →
    QVRAt a Lv (psi s' z z) u := by
  intro V a Lv s s' _ _ _ _ s0 y0 h ht
  simp only [psi.injEq] at h
  rw [← h.2.1] at ht
  exact absurd ht.1 (T.not_lt_z _)

theorem qFO_lowVG : ∀ (V : T) a Lv s s', QFO a Lv (psi s z z) →
    Lhd V (psi s' z z) (psi s z z) →
    (∀ u, ∀ g ∈ comps u V, g < psi s' z z) → isOT (psi s' z z) = true →
    QFO a Lv (psi s' z z) := by
  intro V a Lv s s' h _ _ _
  exact h

end Ytosk.WfT2X
