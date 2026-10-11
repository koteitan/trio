/-
**基底 SRO[n] の NoGapP・NoGap0PosP・Z0Link。** 基底では行 1 の親の v はすべて 0（`vOpt_par1`）。
-/
import Ytosk.V3PhiGap0
import Ytosk.V3BaseI

namespace Ytosk

open T

theorem subS_z {u : T} (h : SubS z u) : u = z := by
  obtain ⟨w, hw, hu⟩ := h
  cases hw
  rcases hu with rfl | ⟨a, b, c, he, _⟩
  · rfl
  · cases he

theorem noGap_z : NoGap z := by
  intro μ _ u hu _; rw [subS_z hu]; exact T.z_lt_psi _ _ _

theorem noGap0_z : NoGap0 z := by
  intro u hu _; rw [subS_z hu]; exact T.z_lt_psi _ _ _

theorem noGap0Pos_z : NoGap0Pos z := by
  intro a b c h; cases h

section
variable {L : Nat} {β : T}

theorem base_v_par1 {c p : Nat} (hp : par (Mlen L) 1 c = some p) : (bval L β).v p = z := by
  have := vOpt_par1 (L := L) (β := β) c
  rw [hp] at this; exact this

theorem base_vP {Q : T → Prop} (hQ : Q z) : VP Q (Mlen L) (bval L β) := by
  intro c p _ hp; rw [base_v_par1 hp]; exact hQ

theorem base_noGapP : NoGapP (Mlen L) (bval L β) := base_vP noGap_z

theorem base_noGap0PosP : NoGap0PosP (Mlen L) (bval L β) := base_vP noGap0Pos_z

theorem base_z0Link : Z0Link (Mlen L) (bval L β) := by
  intro c p hc _ _ hch _ _ _
  obtain ⟨c', _, hp⟩ := hch.has_child hc
  rw [base_v_par1 hp]; exact noGap0_z

end

end Ytosk
