/-
**VSmallR を使わない最上位（2026-10-12、drop-fix）。**

- VSmallR（RClaim の仮定）は標準形で偽（t2 の M13）。落とす補題は RClaim を使わない `drop_all_H` に戻し、
  難しい枠の条件 `HardArg`（M.take x の枠、両方が書き換え・同じ添字・v(i) < s・高い部分が下がる枠で
  comps_{v(i)}(y′) ≤ H(s, y′)、t0-exp・t2 の N 側の `HardArgN` と同じ形）を大域の仮定 `DropResH` に入れる。
- hLast の 11 欄は PH3cG（G3 の切り口）と `TP1ResG`（V3TP1CutG の残り）で述べる（`rest_take_ofG`）。
- 最上位 `trio_terminates_main_GH`: `trio_terminates_main_H` の上に、hLast を `inv3V_take_of`・`rest_take_ofG`、
  Res3H を大域の DropResH・seed・AbsSR で組む。hVSR・hVSRexp はない。
-/
import Ytosk.V3RestTake
import Ytosk.V3TP1CutG
import Ytosk.V3PIntG
import Ytosk.V3DropH

namespace Ytosk

open T

/-- The matrix-wise residuals of TP1C・TP1WC・TrigOmC over PH3cG. -/
def TP1ResG (N : Mat) (σ : Valn) : Prop := TP1LeafG N σ ∧ TP1WLeafG N σ ∧ TrigCutG N σ

/-- **The eleven hole fields of `M.take x`** (PH3cG version). -/
theorem rest_take_ofG (hFrm : FrmLF) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M)
    (hl : 2 ≤ M.length) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hPH : PH3cG M ρ) (hNG : NoGapP M ρ) (hP0 : PhiX0R M ρ)
    (hD0 : DropPhi0Res M (M.length - 1) ρ (drop1 M (M.length - 1) rk))
    (hTP : TP1ResG (M.take (M.length - 1)) (drop1 M (M.length - 1) rk))
    (h3 : TakeRest3 M rk) :
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
  have hdrop := drop_all hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.vs R.drop.vst
    I.fc I.fo R.drop.argT
    (bump_drop hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.kd I.td R.drop.ab R.drop.ws)
    R.drop.ua
  have hPH1 : PH3cG (M.take x) σ :=
    G.ph3c_drop1 hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank I.good hdrop hPH
  have hO1 : GoodOT (M.take x) σ := V.g.toOT
  have hPX := (phiX_take hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 hNG hP0 hD0).1
  have hAD : AbsD (M.take x) σ := absD_of_phiX hPX
  have hS' : M.take x ≠ SRO := ne_SRO_of_rk hRk1
  have hM' : Std (M.take x) := std_take hM x (by omega)
  have FV : FrameV (M.take x) σ := ⟨sInv_std hM' hS', hC1, V.g, V.kd, V.td, hAD, h3.tplo⟩
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hFrm _ σ hM' hS' FV
  exact ⟨hAD, absU_of_phiX hC1 V.g hPX, tp1C_of_ph3cG hC1 hO1 hPH1 hTP.1, h3.tplo,
    tp1WC_of_ph3cG hC1 hO1 hPH1 hTP.2.1, tplow_of_lf FV f1 f2, h3.auw,
    absDW_of_lf FV f3 f4, trigOmC_of_ph3cG hC1 hO1 hPH1 hTP.2.2, tplon_of_lf FV f1 f5 f6, h3.adn⟩

/-- **The top theorem without `VSmallR`** (2026-10-12): the drop residual is `DropResH` (`HardArg` of
`M.take x` instead of `VSmallR` + `RClaim`), the hole fields of `M.take x` as in `rest_take_ofG`. -/
theorem trio_terminates_main_GH
    (hDH : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V M ρ rk →
      DropResH M (M.length - 1) ρ (drop1 M (M.length - 1) rk))
    (hSeed : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V M ρ rk → SeedR M ρ rk)
    (hAbS : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V M ρ rk → AbsSR M ρ)
    (hFrm : FrmLF)
    (hPH : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → PH3cG M ρ)
    (hTP : ∀ N σ rk, Std N → N ≠ SRO → Rk N rk → Cons N σ → TP1ResG N σ)
    (hNG : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → NoGapP M ρ)
    (hP0 : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → PhiX0R M ρ)
    (hD0 : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      DropPhi0Res M (M.length - 1) ρ (drop1 M (M.length - 1) rk))
    (h3 : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk → TakeRest3 M rk)
    (hExp : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3V (expand M n) ρN rkN)
    (hR2 : ∀ M ρ rk, Std M → Inv3 M ρ rk → Res3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → Res3T2 M ρ rk) :
    WellFounded Step' := by
  apply trio_terminates_main_H _ _ hR2
  · intro M ρ rk hM hS hl I R
    have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
    have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
    have hRest : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
        let x := M.length - 1
        let σ := drop1 M x rk
        AbsD (M.take x) σ ∧ AbsU (M.take x) σ ∧ TP1C (M.take x) σ ∧ TPLo (M.take x) σ ∧
        TP1WC (M.take x) σ ∧ TPLoW (M.take x) σ ∧ AbsUW (M.take x) σ ∧ AbsDW (M.take x) σ ∧
        TrigOmC (M.take x) σ ∧ TPLoN (M.take x) σ ∧ AbsDN (M.take x) σ := by
      intro M ρ rk hM hS hl I R
      have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
      have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
      exact rest_take_ofG hFrm hM hl I R (hPH M ρ rk hM hS I R) (hNG M ρ rk hM hS I R)
        (hP0 M ρ rk hM hS I R) (hD0 M ρ rk hM hS hl I R)
        (hTP _ _ rk (std_take hM _ (by omega)) (ne_SRO_of_rk hRk1) hRk1 (cons_of_rk hRk1))
        (h3 M ρ rk hM hS hl I R)
    have V := inv3V_take_of hRest M ρ rk hM hS hl I R
    have hne : M.take (M.length - 1) ≠ [] := by
      intro h; have := congrArg List.length h; rw [List.length_take] at this; simp at this; omega
    have hS' : M.take (M.length - 1) ≠ SRO := ne_SRO_of_rk V.rank
    have hM' := std_take hM (M.length - 1) (by omega)
    exact ⟨_, rk, V, hDH _ _ _ hM' hS' hne V, hSeed _ _ _ hM' hS' hne V, hAbS _ _ _ hM' hS' hne V⟩
  · intro M ρ rk hM hS hE I R hz n hn hNS hNE
    obtain ⟨ρN, rkN, V⟩ := hExp M ρ rk hM hS hE I R hz n hn hNS hNE
    have hMN := Std.exp n hM
    exact ⟨ρN, rkN, V, hDH _ _ _ hMN hNS hNE V, hSeed _ _ _ hMN hNS hNE V, hAbS _ _ _ hMN hNS hNE V⟩

end Ytosk
