/- The zero-tail problem also occurs in OmSide1 and the single-layer branch. -/
import Ytosk.V3QRLocFalse
import Ytosk.WfQrH4

namespace Ytosk.QRQuantifiers
open T WfQrH4 QRLocFalse

theorem zero_tail_base : DQ z false om2 z := by
  have h := DQ.base (η := z) (l := om2) (by decide : fsD om2 z < om2)
  simpa [om2,one,fsD,succ,app] using h

/-- The old single-layer guard still quantifies over the artificial zero tail. -/
theorem not_omSide1 : ¬ OmSide1 z om2 om1 := by
  intro h
  have hq := h.2.2.2.1 (succ one) z rfl z om2 z om1
    (by simp [app]) ⟨succ one,z,rfl⟩ (by simp [app]) zero_tail_base
  exact (by decide : om1 ≠ z) hq

/-- The fallback branches do not rescue this pure layer pair. This is not a
claim that the pair occurs as an actual bump frame in a standard matrix. -/
theorem not_layerF : ¬ LayerF om2 om1 := by
  intro h
  rcases h with ⟨hy,_⟩ | ⟨_,_,_,_,a,b,c,he,hc⟩ | hO | hN
  · exact (by decide : ¬ om2 < E0) hy
  · have hz : c = z := ((T.psi.inj he).2.2).symm
    exact hc hz
  · exact not_omSide1 (hO z zero_tail)
  · rcases hN with ⟨he,_,_⟩ | ⟨a,B,bN,he,_⟩
    · exact (by decide : om2 ≠ E0) he
    · have hz : app B (psi (succ a) z z) = z := ((T.psi.inj he).2.1).symm
      exact (by simp : psi (succ a) z z ≠ z) (app_eq_z hz).2

/-- Even two single last summands do not justify transferring an arbitrary
DQ proof to those last summands: two drops to one, but both last terms are one. -/
theorem repeated_last (η : T) : DQ η true two one := by
  have h0 : DQ η false one z := by
    have h := DQ.base (η := η) (l := one) (by simp [one,fsD] : fsD one η < one)
    simpa [one,fsD] using h
  have h := DQ.mk (B := one) (Q := z) rfl h0 (by simp [summands])
  simpa [two,one,app] using h

theorem not_last_transfer (η : T) : ¬ DQ η false (last two) (last one) := by
  intro h
  have hh := h.lt
  have he : last two = one := by rfl
  rw [he] at hh
  exact lt_irrefl' one hh

end Ytosk.QRQuantifiers
