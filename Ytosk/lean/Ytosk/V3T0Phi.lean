/-
**3 行・t = 0: N = M[n] の AbsD・AbsU を groupA の NoGapP ∧ PhiX0R から。**

チームの決定（groupA、V3PhiGap）: AbsD・AbsU は NoGapP ∧ PhiX0R の形で運ぶ。
- NoGapP N は M の NoGapP から証明（M.take x へは noGapP_take、N へは groupA の noGapP_t0）。
- PhiX0R N は残り（groupA が t = 0 で証明中）。
M の NoGapP は仮定（最終的に運ぶ不変条件に入る）。
-/
import Ytosk.V3T0VS2
import Ytosk.V3PhiGapT0

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **A residual value field of `N` given `NoGapP` of `M`.** -/
def T0FieldG (F : Mat → Valn → Prop) : Prop :=
  ∀ M ρ rk r L n σ rkN, T0Ctx M ρ rk r L n σ rkN → NoGapP M ρ → F (TRIO.gexp M r L 0 0 n) σ

/-- **`NoGapP` of `N = M[n]`** (`t = 0`) from that of `M`. -/
theorem t0_noGapP : T0FieldG NoGapP := by
  intro M ρ rk r L n σ rkN hctx hNG
  obtain ⟨_, _, I, R, hlen, hL, hp, he1, _, hn2, hCN, hRN, _⟩ := id hctx
  have hn : 1 ≤ n := by omega
  have hx : r + L + 1 = M.length := hlen
  have hx2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hcnt := hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1
  have hoff := chg_off hx I.cons I.good hC1 hRk1
  have hlN : (TRIO.gexp M r L 0 0 n).length = r + n * L := lenN0 hlen hn
  have hvC := t0_vals hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hn2 (depLike_chgX M (r + L))
    (read_not_chg hlen hL hp I.r0p I.z2 I.sd I.z1 I.uat I.uab) I.cons I.good hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hvD := t0_vals hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hn2 (depLike_depX M (r + L))
    (read_not_dep hlen hL hp I.r0p I.z2 I.sd I.z1 I.uat I.uab) I.cons I.good hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hNT : NoGapP (M.take (r + L)) (drop1 M (r + L) rk) :=
    noGapP_take hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 hNG
  exact noGapP_t0 hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab hNG hNT
    (fun i hi hd => by
      rw [(hvD i (by rw [hlN]; omega)).2 (fun h' => hd h'.2), tau_v_lt hi])
    (fun i hri hiN => (hvC i hiN).2 (fun h => by omega))

/-- `AbsD` of `N` from `NoGapP` (proved) and the residual `PhiX0R` of `N`. -/
theorem t0_absD (hPhi : T0FieldG PhiX0R) : T0FieldG AbsD := fun M ρ rk r L n σ rkN hctx hNG =>
  absD_of_phiX (phiX_of_noGapR (t0_noGapP M ρ rk r L n σ rkN hctx hNG) (hPhi M ρ rk r L n σ rkN hctx hNG))

/-- `AbsU` of `N` likewise. -/
theorem t0_absU (hPhi : T0FieldG PhiX0R) : T0FieldG AbsU := fun M ρ rk r L n σ rkN hctx hNG => by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hCN, _, hGN, _⟩ := id hctx
  exact absU_of_phiX hCN hGN
    (phiX_of_noGapR (t0_noGapP M ρ rk r L n σ rkN hctx hNG) (hPhi M ρ rk r L n σ rkN hctx hNG))

/-- `T0RestH2` with `VSmallF` in the last-summand form and `AbsD`・`AbsU` from `PhiX0R` (given `NoGapP M`). -/
structure T0RestG : Prop where
  vsD : T0VSResD2
  phi : T0FieldG PhiX0R
  tplo : T0FieldG TPLo
  auw : T0FieldG AbsUW
  tplon : T0FieldG TPLoN
  adn : T0FieldG AbsDN
  tplow : T0FieldG TPLoW
  adw : T0FieldG AbsDW

/-- **`hExp` for `t = 0`, the current residuals**, with `NoGapP` of the standard matrices as a hypothesis
(`hNG`, groupA's carried invariant). -/
theorem hExp_t0_mainG
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hNG : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → NoGapP M ρ)
    (hIV : T0IVRes) (hII : T0IIRes) (hG : T0VSResG) (hS : T0ShapeR3) (hRest : T0RestG) (hC1 : T0RWResC PTP1) (hC1W : T0RWResC PTP1W)
    (hCT : T0RWResC PTrig) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN := by
  have g : ∀ F, T0FieldG F → T0Field F := fun F h M ρ rk r L n σ rkN hctx =>
    h M ρ rk r L n σ rkN hctx (hNG M ρ rk hctx.1 hctx.2.1 hctx.2.2.1 hctx.2.2.2.1)
  exact hExp_t0_mainN2 hLast hIV hII hG hS hRest.vsD (fun hD =>
    ⟨hD, g _ (t0_absD hRest.phi), g _ (t0_absU hRest.phi), g _ hRest.tplo, g _ hRest.auw, g _ hRest.tplon,
      g _ hRest.adn, g _ hRest.tplow, g _ hRest.adw⟩) hC1 hC1W hCT

end Ytosk
