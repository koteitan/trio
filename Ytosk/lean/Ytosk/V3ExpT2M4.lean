/-
**3 行・t = 2: hExp の t = 2 の部分を trio_terminates_main_G の形で（`hExp_t2_G`）。**

main_G では展開は M[n] の Inv3V だけを出せばよい（Res3 の欄は大域の仮定 hDR・hSeed・hVSR から）。
接頭辞 M.take x の Inv3 ∧ Res3A は main_G と同じ大域の仮定から出る（`hLastA_of_G`）。
-/
import Ytosk.V3ExpT2M3
import Ytosk.V3DropRH
import Ytosk.V3InvW

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- **The one-column drop with `Res3A`**, from the global hypotheses of `trio_terminates_main_G`. -/
theorem hLastA_of_G
    (hVSR : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V M ρ rk → VSmallR M ρ)
    (hDR : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V M ρ rk →
      DropResR M (M.length - 1) ρ (drop1 M (M.length - 1) rk))
    (hSeed : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V M ρ rk → SeedR M ρ rk)
    (hAbS : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V M ρ rk → AbsSR M ρ)
    (hRest : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      let x := M.length - 1
      let σ := drop1 M x rk
      AbsD (M.take x) σ ∧ AbsU (M.take x) σ ∧ TP1C (M.take x) σ ∧ TPLo (M.take x) σ ∧
      TP1WC (M.take x) σ ∧ TPLoW (M.take x) σ ∧ AbsUW (M.take x) σ ∧ AbsDW (M.take x) σ ∧
      TrigOmC (M.take x) σ ∧ TPLoN (M.take x) σ ∧ AbsDN (M.take x) σ) :
    ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk' := by
  intro M ρ rk hM hS hl I R
  have V := inv3V_take_of hRest M ρ rk hM hS hl I R
  have hne : M.take (M.length - 1) ≠ [] := by
    intro h; have := congrArg List.length h; rw [List.length_take] at this; simp at this; omega
  have hS' : M.take (M.length - 1) ≠ SRO := ne_SRO_of_rk V.rank
  have hM' := std_take hM (M.length - 1) (by omega)
  exact ⟨_, rk, V, Res3A.ofR hne (sInv_std hM' hS') V (hVSR _ _ _ hM' hS' hne V)
    ⟨hDR _ _ _ hM' hS' hne V, hSeed _ _ _ hM' hS' hne V, hAbS _ _ _ hM' hS' hne V⟩⟩

/-- **`hExp` for `t = 2` in the shape of `trio_terminates_main_G`**: with the global hypotheses of `main_G`
for the prefix `M.take x`. -/
theorem hExp_t2_G
    (hVSR : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V M ρ rk → VSmallR M ρ)
    (hDR : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V M ρ rk →
      DropResR M (M.length - 1) ρ (drop1 M (M.length - 1) rk))
    (hSeed : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V M ρ rk → SeedR M ρ rk)
    (hAbS : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V M ρ rk → AbsSR M ρ)
    (hRest : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      let x := M.length - 1
      let σ := drop1 M x rk
      AbsD (M.take x) σ ∧ AbsU (M.take x) σ ∧ TP1C (M.take x) σ ∧ TPLo (M.take x) σ ∧
      TP1WC (M.take x) σ ∧ TPLoW (M.take x) σ ∧ AbsUW (M.take x) σ ∧ AbsDW (M.take x) σ ∧
      TrigOmC (M.take x) σ ∧ TPLoN (M.take x) σ ∧ AbsDN (M.take x) σ)
    (hB : T2BelowXRes) (hR3 : T2Rest3) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN :=
  hExp_t2_of_lastV (hLastA_of_G hVSR hDR hSeed hAbS hRest) hB hR3

end Ytosk
