/-
**3 行・t = 0: 残りの組み立て。**

前の版の仮定 NoVB（t = 0 で e2(r) ≠ 0 なら 1 列落としで v(r) は変わらない）は標準形で偽だった
（例 (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,1,0)(4,0,0)、bms で標準形かつ SRO より下）。
(iv) は「中間の写しの根がどれも数えられないとき、g の古い枠は r で書き換えない」に替えた（`T0IVRes`、
C′ の 383 件と、NoVB を破る Std の行列での 8 件で例外 0）。VSmallF の g の残り `T0VSResG` はそのまま仮定に残す。
-/
import Ytosk.V3T0VS

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **(iv)**: with no middle copy root counted at `g`, the old frame of `g` does not rewrite at `r`. -/
def T0IVRes : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    ∀ n, 2 ≤ n → ∀ g, par M 0 r = some g →
      Counted M g r → (∀ k, k + 1 < n → ¬ Counted (TRIO.gexp M r L 0 0 n) g (r + k * L)) →
      ∀ Lc0 : List Nat, CL M g = Lc0 ++ [r] → ∀ s y, ρ.o r = psi s y z →
        ¬ (lt (spArg (ρ.v g) z (sumN (Lc0.map ρ.o))) y = true ∧ lt (psi (ρ.v g) z z) (psi s y z) = true)

/-- **The class residuals without (iv)**: (i) at nonzero states and (ii). -/
def T0ShapeR3 : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    (∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] → DepX M (r + L) true c →
      ∀ s y y', ρ.o c = psi s y z → σ.o c = psi s y' z → Lhd z y' y →
      (split y' (psi (succ s) z z)).2 = z → (split y (psi (succ s) z z)).2 = z →
      spArg (ρ.v i) z (sumN (Lc.map ρ.o)) ≠ z →
      Trig (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y →
      lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y' = true) ∧
    (∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] → DepX M (r + L) true c →
      σ.v c ≠ ρ.v c → par M 1 c ≠ some i → ¬ psi (ρ.v c) z z < psi (succ (ρ.v i)) z z →
      ¬ psi (σ.v c) z z < psi (succ (ρ.v i)) z z)

theorem t0ShapeR2_of (hIV : T0IVRes) (h : T0ShapeR3) : T0ShapeR2 := by
  intro M ρ rk r L hM hS I R hlen hL hp he1
  obtain ⟨h1, h2⟩ := h M ρ rk r L hM hS I R hlen hL hp he1
  exact ⟨h1, h2, hIV M ρ rk r L hM hS I R hlen hL hp he1⟩

/-- `T0RestH` with `VSmallF` reduced to the residual `T0VSResD`. -/
structure T0RestH2 : Prop where
  vsD : T0VSResD
  ad : T0Field AbsD
  au : T0Field AbsU
  tplo : T0Field TPLo
  auw : T0Field AbsUW
  tplon : T0Field TPLoN
  adn : T0Field AbsDN
  tplow : T0Field TPLoW
  adw : T0Field AbsDW
  res : T0Res3H

theorem T0RestH2.toRestH (hG : T0VSResG) (h : T0RestH2) : T0RestH :=
  ⟨t0_vsmallF h.vsD hG, h.ad, h.au, h.tplo, h.auw, h.tplon, h.adn, h.tplow, h.adw, h.res⟩

/-- **`hExp` for `t = 0`, the current residuals**: `T0IVRes`, `T0VSResG`, the class residuals
`T0ShapeR3` ((i) at nonzero states, (ii)), `T0RestH2` (`T0VSResD`, the other value fields, `Res3H`), and the
shadow frames `T0RWResC`. -/
theorem hExp_t0_mainN
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hIV : T0IVRes) (hG : T0VSResG) (hS : T0ShapeR3) (hRest : T0RestH2) (hC1 : T0RWResC PTP1) (hC1W : T0RWResC PTP1W)
    (hCT : T0RWResC PTrig) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN :=
  hExp_t0_mainH hLast (t0ShapeR2_of hIV hS) (hRest.toRestH hG) hC1 hC1W hCT

end Ytosk
