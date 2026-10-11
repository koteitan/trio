/-
**PH3cG・FC3 を他の担当の組み立てに差し込むためのつなぎ（closure、2026-10-11）。**

- 評価の取り替え（`ph3c_congr`・`fc3_congr`）: 同じ行列の評価が一致すれば同じ。
- 1 列落とし M → M.take x の drop1 評価（`ph3c_drop1`・`fc3_drop1`）: 落とす補題の結論（PO・PV、
  `drop_all`・`drop_all_H` などのどれから出してもよい）を受け取る形。
- M.take x のどの評価でも（`ph3c_take_any`・`fc3_take_any`、順位による一意性）。t = 2 の `hT` の形。
-/
import Ytosk.V3PT2G
import Ytosk.V3PDropG
import Ytosk.V3Top
import Ytosk.V3PKindG

namespace Ytosk.G

open T

theorem ph3c_congr {N : Mat} {σ τ : Valn} (h : PH3cG N σ) (hA : Agree N σ τ) : PH3cG N τ :=
  ph3c_iff.mpr (clField_congr (Q := QPH) (ph3c_iff.mp h) hA)

theorem fc3_congr {N : Mat} {σ τ : Valn} (h : FC3 N σ) (hA : Agree N σ τ) : FC3 N τ :=
  fc3_iff.mpr (clField_congr (Q := QF3) (fc3_iff.mp h) hA)

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  {ρ : Valn} {rk : Bool → Nat → Nat} (hC : Cons M ρ) (hRM : Rk M rk) (hG : Good3 M ρ)
  (hdrop : ∀ i, i < x → PO ρ (drop1 M x rk) i ∧ PV M ρ (drop1 M x rk) i)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hRM hG hdrop

theorem rk_drop1 : Rk (M.take x) rk := by
  have hcnt := counted_take_last (M := M) (by omega) hR0 hZ2 hSD hZ1 hUAT
  rw [show M.length - 1 = x by omega] at hcnt
  exact rk_take (by omega) hRM hcnt

/-- **PH3cG of `M.take x` with the drop valuation.** -/
theorem ph3c_drop1 (hP : PH3cG M ρ) : PH3cG (M.take x) (drop1 M x rk) := by
  have hRk1 := rk_drop1 hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hRM hG hdrop
  exact ph3c_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG (cons_of_rk hRk1) hRk1 hdrop hP

theorem fc3_drop1 (hP : FC3 M ρ) : FC3 (M.take x) (drop1 M x rk) := by
  have hRk1 := rk_drop1 hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hRM hG hdrop
  exact fc3_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG (cons_of_rk hRk1) hRk1 hdrop hP

/-- **PH3cG of `M.take x` with any valuation.** -/
theorem ph3c_take_any (hP : PH3cG M ρ) : ∀ τ, Cons (M.take x) τ → PH3cG (M.take x) τ := by
  intro τ hτ
  have hRk1 := rk_drop1 hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hRM hG hdrop
  exact ph3c_congr (ph3c_drop1 hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hRM hG hdrop hP)
    (agree_of_cons (cons_of_rk hRk1) hτ hRk1)

theorem fc3_take_any (hP : FC3 M ρ) : ∀ τ, Cons (M.take x) τ → FC3 (M.take x) τ := by
  intro τ hτ
  have hRk1 := rk_drop1 hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hRM hG hdrop
  exact fc3_congr (fc3_drop1 hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hRM hG hdrop hP)
    (agree_of_cons (cons_of_rk hRk1) hτ hRk1)

end

end Ytosk.G
