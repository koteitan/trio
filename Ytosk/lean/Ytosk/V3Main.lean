/-
**3 行のバシク行列（z < 2 を含む SRO からの展開）の停止性: 現在の最上位の定理。**

基底 SRO[n]（V3BaseInd）と t = 2 の降下（V3T2Fin、残りは `Res3T2`）を差し込んだ形。
残りの仮定:
- `hLast`: 1 列落とし `M → M.take (len − 1)` で値の部分 `Inv3V` と `Res3A` が移る。
- `hExp`: n ≥ 2 の展開 `M → M[n]` で同じく移る。
- `hR2`: t = 2 の残りの事実 `Res3T2`。
-/
import Ytosk.V3BaseInd
import Ytosk.V3T2Fin

namespace Ytosk

theorem trio_terminates_main_T2 (hU0 : OldUpgAbs)
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hExp : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3V (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN)
    (hR2 : ∀ M ρ rk, Std M → Inv3 M ρ rk → Res3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → Res3T2 M ρ rk) :
    WellFounded Step' :=
  (trio_terminates_final_T2 hU0) hBaseV_holds hLast hExp hR2

end Ytosk
