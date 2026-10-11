/-
**hLast の M.take x の 11 欄を減らす（2026-10-12、drop-fix）。**

`inv3V_take_of` の `hRest`（M.take x の 11 欄）を、既存の補題でつないで次の残りに減らす。
- AbsD・AbsU: PhiX から（`absD_of_phiX`・`absU_of_phiX`）。PhiX (M.take x) は M の NoGapP・PhiX0R と
  段 0 の落としの残り DropPhi0Res から（groupA の `phiX_take`）。
- TPLoW・AbsDW・TPLoN: M.take x 自身の FrameV（AbsD・TPLo を含む）と、行列ごとの LevFree の残り
  `FrmLF`（t0-exp・t1-exp と共通の大域の仮定）から（`tplow_of_lf`・`absDW_of_lf`・`tplon_of_lf`）。
- 残り 6 欄（M.take x の TPLo・TP1C・TP1WC・TrigOmC・AbsUW・AbsDN）は仮定 `TakeRest6`。

あわせて、DropResR の欄 TailNR（tnr）は仮定なしで成り立つ（`tailY_holds`、V3TailY）ので、それを外した
`DropResS` で述べた最上位 `trio_terminates_main_GR` を置く。
-/
import Ytosk.V3DropRH
import Ytosk.V3PhiGap
import Ytosk.V3ExpT1L
import Ytosk.V3T0LF
import Ytosk.V3MainGP
import Ytosk.V3TailY

namespace Ytosk

open T

/-- **The six fields of `M.take x` that remain** (the drop valuation `σ = drop1 M x rk`). -/
structure TakeRest6 (M : Mat) (rk : Bool → Nat → Nat) : Prop where
  tplo : TPLo (M.take (M.length - 1)) (drop1 M (M.length - 1) rk)
  tp1 : TP1C (M.take (M.length - 1)) (drop1 M (M.length - 1) rk)
  tp1w : TP1WC (M.take (M.length - 1)) (drop1 M (M.length - 1) rk)
  trig : TrigOmC (M.take (M.length - 1)) (drop1 M (M.length - 1) rk)
  auw : AbsUW (M.take (M.length - 1)) (drop1 M (M.length - 1) rk)
  adn : AbsDN (M.take (M.length - 1)) (drop1 M (M.length - 1) rk)

/-- **The eleven hole fields of `M.take x`** from `NoGapP`・`PhiX0R` of `M`, the level-0 drop residual
`DropPhi0Res`, the matrix-wise `FrmLF`, and the six fields `TakeRest6`. -/
theorem rest_take_of (hFrm : FrmLF) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M)
    (hl : 2 ≤ M.length) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hNG : NoGapP M ρ) (hP0 : PhiX0R M ρ)
    (hD0 : DropPhi0Res M (M.length - 1) ρ (drop1 M (M.length - 1) rk))
    (h6 : TakeRest6 M rk) :
    let x := M.length - 1
    let σ := drop1 M x rk
    AbsD (M.take x) σ ∧ AbsU (M.take x) σ ∧ TP1C (M.take x) σ ∧ TPLo (M.take x) σ ∧
    TP1WC (M.take x) σ ∧ TPLoW (M.take x) σ ∧ AbsUW (M.take x) σ ∧ AbsDW (M.take x) σ ∧
    TrigOmC (M.take x) σ ∧ TPLoN (M.take x) σ ∧ AbsDN (M.take x) σ := by
  intro x σ
  have hx : x + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take x) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have hVI : ValInv M ρ := ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩
  have V := valInv_drop1 hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank hVI R.drop
  have hPX := (phiX_take hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 hNG hP0 hD0).1
  have hAD : AbsD (M.take x) σ := absD_of_phiX hPX
  have hS' : M.take x ≠ SRO := ne_SRO_of_rk hRk1
  have hM' : Std (M.take x) := std_take hM x (by omega)
  have FV : FrameV (M.take x) σ := ⟨sInv_std hM' hS', hC1, V.g, V.kd, V.td, hAD, h6.tplo⟩
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hFrm _ σ hM' hS' FV
  exact ⟨hAD, absU_of_phiX hC1 V.g hPX, h6.tp1, h6.tplo, h6.tp1w, tplow_of_lf FV f1 f2, h6.auw,
    absDW_of_lf FV f3 f4, h6.trig, tplon_of_lf FV f1 f5 f6, h6.adn⟩

/-- **`DropResR` without the tail field** (`TailY` holds by `tailY_holds`). -/
structure DropResS (N : Mat) (x : Nat) (σ σ' : Valn) : Prop where
  vst : VSmallNew N x σ σ'
  ws : BumpWeakSrc N x σ σ'
  ua : UpgAbsX N x σ
  ab : BumpAbsC N x σ
  vnr : VSmallNewR N x σ σ'
  sh : ShadowC N x σ σ'

theorem DropResS.toR {N : Mat} {x : Nat} {σ σ' : Valn} {rk : Bool → Nat → Nat} (hx : x + 1 = N.length)
    (S : SInv N) (hC : Cons N σ) (hG : Good3 N σ) (hR : Rk N rk) (h : DropResS N x σ σ') :
    DropResR N x σ σ' :=
  ⟨h.vst, h.ws, h.ua, h.ab, h.vnr, h.sh, tailY_holds hx S.r0p S.z2 S.sibDec S.z1c hC hG hR⟩

/-- **The top theorem with the drop fields reduced** (2026-10-12): as `trio_terminates_main_GP`, with
`hRest` replaced by `NoGapP`・`PhiX0R` of the standard matrices, the level-0 drop residual `DropPhi0Res`,
the matrix-wise `FrmLF` and the six fields `TakeRest6`, and `DropResR` by `DropResS` (no tail field). -/
theorem trio_terminates_main_GR
    (hDR : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V M ρ rk →
      DropResS M (M.length - 1) ρ (drop1 M (M.length - 1) rk))
    (hSeed : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V M ρ rk → SeedR M ρ rk)
    (hAbS : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V M ρ rk → AbsSR M ρ)
    (hFrm : FrmLF)
    (hNG : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → NoGapP M ρ)
    (hP0 : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → PhiX0R M ρ)
    (hD0 : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      DropPhi0Res M (M.length - 1) ρ (drop1 M (M.length - 1) rk))
    (h6 : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk → TakeRest6 M rk)
    (hExp : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk → VSmallR M ρ →
      col M (M.length - 1) ≠ (0, 0, 0) → ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3V (expand M n) ρN rkN)
    (hVSRexp : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk → VSmallR M ρ →
      col M (M.length - 1) ≠ (0, 0, 0) → ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∀ ρN rkN, Inv3V (expand M n) ρN rkN → VSmallR (expand M n) ρN)
    (hR2 : ∀ M ρ rk, Std M → Inv3 M ρ rk → Res3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → Res3T2 M ρ rk) :
    WellFounded Step' := by
  apply trio_terminates_main_GP _ hSeed hAbS _ hExp hVSRexp hR2
  · intro M ρ rk hM hS hE V
    have hl : 0 < M.length := by
      cases M with
      | nil => exact absurd rfl hE
      | cons _ _ => simp
    exact (hDR M ρ rk hM hS hE V).toR (by omega) (sInv_std hM hS) V.cons V.good V.rank
  · intro M ρ rk hM hS hl I R
    exact rest_take_of hFrm hM hl I R (hNG M ρ rk hM hS I R) (hP0 M ρ rk hM hS I R) (hD0 M ρ rk hM hS hl I R)
      (h6 M ρ rk hM hS hl I R)

end Ytosk
