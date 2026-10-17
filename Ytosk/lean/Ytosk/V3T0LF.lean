/-
**3 行・t = 0: N = M[n] の最後の列の枠の欄 TPLoW・AbsDW・TPLoN を運ばずに出す。**

t1-exp の tplow_of_lf・absDW_of_lf・tplon_of_lf はどの行列でも使える。N 自身の FrameV（AbsD・TPLo は
V3T0Phi・V3T0Col で出したもの）と、行列ごとの LevFree の残り `FrmLF`（段 μ ≠ 0 の LevFree と段 0 の部分。
t1-exp の hFrm から VKFree を外した形で、t によらない）から出す。
-/
import Ytosk.V3T0Col
import Ytosk.V3ExpT1L

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The matrix-wise residual of the last-column frame fields** (t1-exp's `hFrm` without `VKFree`): the
`LevFree` parts at a level `μ ≠ 0` and the parts at the level `0`, for every standard matrix. -/
def FrmLF : Prop :=
  ∀ N σ, Std N → N ≠ SRO → FrameV N σ →
    TPLoWLF N σ ∧ TPLoW0 N σ ∧ AbsDWLF N σ ∧ AbsDW0 N σ ∧ TPLoNSeed N σ ∧ TPLoN0 N σ

/-- `FrameV` of `N = M[n]` (`t = 0`) from its `AbsD` and `TPLo`. -/
theorem t0_frameV (hAD : T0FieldG AbsD) (hTP : T0FieldG TPLo) :
    ∀ M ρ rk r L n σ rkN, T0Ctx M ρ rk r L n σ rkN → NoGapP M ρ → FrameV (TRIO.gexp M r L 0 0 n) σ := by
  intro M ρ rk r L n σ rkN hctx hNG
  obtain ⟨hM, _, I, _, hlen, hL, hp, he1, _, _, hCN, hRN, hGN, _, _, hKD, hTD⟩ := id hctx
  exact ⟨sInv_std (std_gexp_t0 hM I hlen hL hp he1 n) (ne_SRO_of_rk hRN), hCN, hGN, hKD, hTD,
    hAD M ρ rk r L n σ rkN hctx hNG, hTP M ρ rk r L n σ rkN hctx hNG⟩

/-- **TPLoW・AbsDW・TPLoN of `N = M[n]`** (`t = 0`) from `FrmLF` and `N`'s own `AbsD`・`TPLo`. -/
theorem t0_frameFields (hF : FrmLF) (hAD : T0FieldG AbsD) (hTP : T0FieldG TPLo) :
    T0FieldG TPLoW ∧ T0FieldG AbsDW ∧ T0FieldG TPLoN := by
  have key : ∀ M ρ rk r L n σ rkN, T0Ctx M ρ rk r L n σ rkN → NoGapP M ρ →
      TPLoW (TRIO.gexp M r L 0 0 n) σ ∧ AbsDW (TRIO.gexp M r L 0 0 n) σ ∧ TPLoN (TRIO.gexp M r L 0 0 n) σ := by
    intro M ρ rk r L n σ rkN hctx hNG
    obtain ⟨hM, _, I, _, hlen, hL, hp, he1, _, _, _, hRN, _⟩ := id hctx
    have FV := t0_frameV hAD hTP M ρ rk r L n σ rkN hctx hNG
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      hF _ σ (std_gexp_t0 hM I hlen hL hp he1 n) (ne_SRO_of_rk hRN) FV
    exact ⟨tplow_of_lf FV h1 h2, absDW_of_lf FV h3 h4, tplon_of_lf FV h1 h5 h6⟩
  exact ⟨fun M ρ rk r L n σ rkN hctx hNG => (key M ρ rk r L n σ rkN hctx hNG).1,
    fun M ρ rk r L n σ rkN hctx hNG => (key M ρ rk r L n σ rkN hctx hNG).2.1,
    fun M ρ rk r L n σ rkN hctx hNG => (key M ρ rk r L n σ rkN hctx hNG).2.2⟩

/-- `T0RestC` without the three last-column frame fields. -/
structure T0RestF : Prop where
  vsD : T0VSResD2
  phi : T0FieldG PhiX0R
  tploR : T0TPLoRes
  auwR : T0AbsUWRes
  adnR : T0AbsDNRes

/-- **`hExp` for `t = 0`, the current residuals**, with TPLoW・AbsDW・TPLoN from the matrix-wise `FrmLF`. -/
theorem hExp_t0_mainF (hU0 : OldUpgAbs)
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hNG : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → NoGapP M ρ) (hFrm : FrmLF)
    (hIV : T0IVRes) (hII : T0IIRes) (hG : T0VSResG) (hS : T0ShapeR3) (hRest : T0RestF) (hC1 : T0RWResC PTP1)
    (hC1W : T0RWResC PTP1W) (hCT : T0RWResC PTrig) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN :=
  have f : ∀ F, T0Field F → T0FieldG F := fun _ h M ρ rk r L n σ rkN hctx _ => h M ρ rk r L n σ rkN hctx
  have hFF := t0_frameFields hFrm (t0_absD hRest.phi) (f _ (t0_tplo hRest.tploR))
  (hExp_t0_mainC2 hU0) hLast hNG hIV hII hG hS
    ⟨hRest.vsD, hRest.phi, hRest.tploR, hRest.auwR, hRest.adnR, hFF.2.2, hFF.1, hFF.2.1⟩ hC1 hC1W hCT

end Ytosk
