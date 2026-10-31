/-
**WfT2X7: `hQlowV` for the frame fields that only speak of rewriting frames (2026-11-01).**

The fourth case of `FrameShapeX` lowers an argument-free last child; such a child does not rewrite (`lt B 0` is
false), so the rewriting-frame fields `QFC` (FrameClosed, V3T0Frm), `QFCo` (V3T2FC), `QVRAt` (VSmallRAll at a level,
V3T2VRA) survive it, and `QFO` (FrameOT) does not read the last child.
-/
import Ytosk.WfT2X6
import Ytosk.V3T2FC
import Ytosk.V3T2VRA

namespace Ytosk.WfT2X

open T Classical Ytosk.WfAbsW

set_option linter.unusedVariables false

theorem qFC_lowV : ∀ a Lv s s', QFC a Lv (psi s z z) → Lhd a (psi s' z z) (psi s z z) →
    isOT (psi s' z z) = true → QFC a Lv (psi s' z z) := by
  intro a Lv s s' _ _ _ s0 y0 h ht
  simp only [psi.injEq] at h
  rw [← h.2.1] at ht; exact absurd ht.1 (T.not_lt_z _)

theorem qFCo_lowV : ∀ a Lv s s', QFCo a Lv (psi s z z) → Lhd a (psi s' z z) (psi s z z) →
    isOT (psi s' z z) = true → QFCo a Lv (psi s' z z) :=
  fun a Lv s s' h hl hot => ⟨hot, qFC_lowV a Lv s s' h.2 hl hot⟩

theorem qVRAt_lowV (u : T) : ∀ a Lv s s', QVRAt a Lv (psi s z z) u → Lhd a (psi s' z z) (psi s z z) →
    isOT (psi s' z z) = true → QVRAt a Lv (psi s' z z) u := by
  intro a Lv s s' _ _ _ s0 y0 h ht
  simp only [psi.injEq] at h
  rw [← h.2.1] at ht; exact absurd ht.1 (T.not_lt_z _)

theorem qFO_lowV : ∀ a Lv s s', QFO a Lv (psi s z z) → Lhd a (psi s' z z) (psi s z z) →
    isOT (psi s' z z) = true → QFO a Lv (psi s' z z) :=
  fun _ _ _ _ h _ _ => h

end Ytosk.WfT2X
