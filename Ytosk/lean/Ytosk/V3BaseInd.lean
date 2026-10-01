/-
**最上位の定理に基底 hBase を差し込む**: `trio_terminates_indV` の hBase を SRO[n] の評価
`bval (1 + 3n) 1`・順位 `brk` で外す（値の項目は V3BaseI、Res3A は V3Base）。
-/
import Ytosk.V3Base
import Ytosk.V3IndV

namespace Ytosk

open T

/-- **The base of the induction, value part**: every `SRO[n]` satisfies `Inv3V` and `Res3A`. -/
theorem hBaseV_holds : ∀ n, expand SRO n ≠ [] →
    ∃ ρ rk, Inv3V (expand SRO n) ρ rk ∧ Res3A (expand SRO n) ρ rk := by
  intro n _
  rw [expand_SRO_eq]
  have hF : BaseFit (1 + 3 * n) one := Or.inl ⟨by omega, rfl⟩
  have hL : 1 ≤ 1 + 3 * n := by omega
  exact ⟨bval (1 + 3 * n) one, brk (1 + 3 * n), ⟨bval_cons hF, base_good3 hF, brk_rk le_rfl,
    base_vsmallF hF, base_frameClosed hF, base_frameOT hF, base_kd hF, base_td hF, base_ad hF,
    base_au hF, base_tp1 hF, base_tplo hF, base_tp1w hF, base_tplow hF, base_auw hF, base_adw hF,
    base_trig hF, base_tplon hF, base_adn hF, base_rootS hF hL, base_rootP hF hL⟩, base_res3A⟩

end Ytosk
