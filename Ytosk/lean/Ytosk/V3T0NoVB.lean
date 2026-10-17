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

/-- **The class residual (i)** at nonzero states. -/
def T0ShapeR3 : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    (∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] → DepX M (r + L) true c →
      ∀ s y y', ρ.o c = psi s y z → σ.o c = psi s y' z → Lhd z y' y →
      (split y' (psi (succ s) z z)).2 = z → (split y (psi (succ s) z z)).2 = z →
      spArg (ρ.v i) z (sumN (Lc.map ρ.o)) ≠ z →
      Trig (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y →
      lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y' = true)

/-- **(ii) as a structural fact**: a counted last child `c` of `i` (before `r`) whose `v` depends on `x`,
with `P_1(c) ≠ i`, sits below a row-2-one `i` with the same `P_1` and no bump child (C′ と T0Ext で例外 0). Then
`v(i) = v(p) + ω < v_N(c)` (`v_lt_of_bump` in `t0_dep_ot`). -/
def T0IIRes : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    ∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] → DepX M (r + L) false c →
      par M 1 c ≠ some i →
      par M 1 i = par M 1 c ∧ entry M 2 i = 1 ∧ ∀ d ∈ children M i, col M d ≠ bump M i

/-- **The structural form of (ii)**: the shape of `c` and of `c + 1` from `dv_shape`, the rest from `T0IIRes`. -/
theorem t0_ii_of (hII : T0IIRes) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk) (hlen : r + L + 1 = M.length)
    (hL : 0 < L) (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0) :
    ∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] → DepX M (r + L) false c →
      par M 1 c ≠ some i →
      entry M 2 c = 0 ∧ upg M c = some (c + 1) ∧ c + 1 < r ∧
      (∃ j ∈ children M (c + 1), col M j = bump M (c + 1)) ∧
      par M 1 i = par M 1 c ∧ entry M 2 i = 1 ∧ ∀ d ∈ children M i, col M d ≠ bump M i := by
  intro i c Lc hi hc hCL hdv hp1
  have hx : r + L + 1 = M.length := hlen
  have hx2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hJ := rowJ_std hM
  have hcCL : c ∈ CL M i := by rw [hCL]; simp
  have hcM : c ∈ children M i := cl_mem_children hcCL
  have hccnt : Counted M i c := by unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
  have hpc : par M 0 c = some i := (mem_children_iff.mp hcM).2
  obtain ⟨h1c, _, hcase⟩ := dv_shape hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hp (by omega) hdv
  rcases hcase with ⟨h2c, hu, hux, hdu⟩ | ⟨h2c, _⟩
  · have hur : c + 1 < r := by
      rcases Nat.lt_or_ge (c + 1) r with h | h
      · exact h
      · exfalso
        have : c + 1 = r := by omega
        rw [this] at hdu
        exact not_depX_v_r hlen hL hp I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hdu
    have h2u : entry M 2 (c + 1) ≠ 0 := by have := upg_target_e2 hu; omega
    obtain ⟨_, _, hcu⟩ := dv_shape hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hp (by omega) hdu
    have hbu : ∃ j ∈ children M (c + 1), col M j = bump M (c + 1) := by
      rcases hcu with ⟨h2, _⟩ | ⟨_, Lb, Kb, j, k, hch, hjb, _⟩
      · exact absurd h2 h2u
      · exact ⟨j, by rw [hch]; simp, hjb⟩
    exact ⟨h2c, hu, hur, hbu, hII M ρ rk r L hM hS I R hlen hL hp he1 i c Lc hi hc hCL hdv hp1⟩
  · exfalso
    have hge : entry M 1 c ≤ entry M 1 i := by
      by_contra hlt; exact hp1 (par1_of_child hpc (by omega))
    have hle := hJ c i h2c hpc
    have hc2 : entry M 2 c = 1 := by have := I.z2 c; omega
    apply hccnt.1
    rw [col_eq_entries, I.r0p c i hpc, hc2]
    unfold bump; congr 2; omega

theorem t0ShapeR2_of (hIV : T0IVRes) (hII : T0IIRes) (h : T0ShapeR3) : T0ShapeR2 := by
  intro M ρ rk r L hM hS I R hlen hL hp he1
  exact ⟨h M ρ rk r L hM hS I R hlen hL hp he1, t0_ii_of hII hM hS I R hlen hL hp he1,
    hIV M ρ rk r L hM hS I R hlen hL hp he1⟩

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

theorem T0RestH2.toRestH (hG : T0VSResG) (h : T0RestH2) : T0RestH :=
  ⟨t0_vsmallF h.vsD hG, h.ad, h.au, h.tplo, h.auw, h.tplon, h.adn, h.tplow, h.adw⟩

/-- **`hExp` for `t = 0`, the current residuals**: `T0IVRes`, `T0VSResG`, the class residuals
`T0ShapeR3` ((i) at nonzero states, (ii)), `T0RestH2` (`T0VSResD`, the other value fields, `Res3H`), and the
shadow frames `T0RWResC`. -/
theorem hExp_t0_mainN (hU0 : OldUpgAbs)
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hIV : T0IVRes) (hII : T0IIRes) (hG : T0VSResG) (hS : T0ShapeR3) (hRest : T0RestH2) (hC1 : T0RWResC PTP1) (hC1W : T0RWResC PTP1W)
    (hCT : T0RWResC PTrig) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN :=
  (hExp_t0_mainH hU0) hLast (t0ShapeR2_of hIV hII hS) (hRest.toRestH hG) hC1 hC1W hCT

end Ytosk
