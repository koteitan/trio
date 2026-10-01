/-
**3 行・t = 2: 最終の停止性定理への接続（HInvE 版）。**

`trio_terminates_final`（V3IndV）の hT2 は HInvE（Std な行列にある評価が 1 つある）を受け取る。
M[n]（n ≥ 2）の評価は `inv_expand_of_E` から取る（Inv3 が Cons・Rk・Good3 を含む）。
t = 2 の残りの仮定は `Res3T2`（V3T2Top）だけ。
-/
import Ytosk.V3IndV
import Ytosk.V3T2Top

namespace Ytosk

open T

/-- **`hT2` of `trio_terminates_final`** from `Res3T2`. -/
theorem t2_hT2E
    (hR2 : ∀ M ρ rk, Std M → Inv3 M ρ rk → Res3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → Res3T2 M ρ rk) :
    HInvE → ∀ M ρ rk, Std M → Inv3 M ρ rk → Res3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ n, DropsAt M ρ n := by
  intro hInv M ρ rk hM I R hz h2
  apply t2_drops I R (hR2 M ρ rk hM I R hz h2) hz h2
  intro n _ _ hE
  obtain ⟨σ, rkN, IN, _⟩ := inv_expand_of_E hInv hM hE
  exact ⟨σ, rkN, IN.cons, IN.rank, IN.good⟩

/-- **Termination of the 3-row BMS from SRO** (`trio_terminates_final` with `t = 2` reduced to `Res3T2`). -/
theorem trio_terminates_final_T2
    (hBase : ∀ n, expand SRO n ≠ [] → ∃ ρ rk, Inv3V (expand SRO n) ρ rk ∧ Res3A (expand SRO n) ρ rk)
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hExp : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3V (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN)
    (hR2 : ∀ M ρ rk, Std M → Inv3 M ρ rk → Res3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → Res3T2 M ρ rk) :
    WellFounded Step' :=
  trio_terminates_final hBase hLast hExp (t2_hT2E hR2)

end Ytosk
