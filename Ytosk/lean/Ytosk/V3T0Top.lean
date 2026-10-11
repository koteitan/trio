/-
**3 行・t = 0: hExp の最上位（2026-10-11 の残り）。**

- (i)（T0ShapeR3）は M の PH3c と T0RERes・T0CutRes から（V3T0Cut）。
- VSmallF の D の残り T0VSResD2 は T0VSOnly から（V3T0VS3）。
- 最後の列の枠の 3 欄は FrmLF から（V3T0LF）。
-/
import Ytosk.V3T0LF
import Ytosk.V3T0Cut
import Ytosk.V3T0VS3
import Ytosk.V3T0VSR

namespace Ytosk

open T

/-- The value residuals of `N` that remain (`T0RestF` without `vsD`). -/
structure T0RestV : Prop where
  phi : T0FieldG PhiX0R
  tploR : T0TPLoRes
  auwR : T0AbsUWRes
  adnR : T0AbsDNRes

/-- **`hExp` for `t = 0`, the current residuals.** -/
theorem hExp_t0_top
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hNG : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → NoGapP M ρ) (hFrm : FrmLF)
    (hPH : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → PH3c M ρ)
    (hIV : T0IVRes) (hII : T0IIRes) (hG : T0VSResG) (hRE : T0RERes) (hCut : T0CutRes) (hOnly : T0VSOnly)
    (hRest : T0RestV) (hC1 : T0RWResC PTP1) (hC1W : T0RWResC PTP1W) (hCT : T0RWResC PTrig) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN :=
  hExp_t0_mainF hLast hNG hFrm hIV hII hG (t0ShapeR3_of hPH hRE hCut)
    ⟨t0VSResD2_of hOnly, hRest.phi, hRest.tploR, hRest.auwR, hRest.adnR⟩ hC1 hC1W hCT

/-- **`hVSRexp` for `t = 0`** with (i) from PH3c and RE. -/
theorem hVSRexp_t0_top
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hPH : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → PH3c M ρ)
    (hIV : T0IVRes) (hII : T0IIRes) (hRE : T0RERes) (hCut : T0CutRes) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk → VSmallR M ρ →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∀ ρN rkN, Inv3V (expand M n) ρN rkN → VSmallR (expand M n) ρN :=
  hVSRexp_t0 hLast hIV hII (t0ShapeR3_of hPH hRE hCut)

end Ytosk
