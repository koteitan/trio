/-
**Inv3V2 の 1 列落としの組み立て。**
構造・値の通常の欄と PH3cG・FC3・VSmallRAll は既存の落とす補題から。
TP1C・TP1WC は PH3cG と葉の残りから出す。偽の TrigCutG は要求しない。
最後の列の枠の欄と AbsDN は残りとして明示する。
-/
import Ytosk.V3Inv2
import Ytosk.V3VSRAllDrop
import Ytosk.V3PIntG
import Ytosk.V3TP1CutG

namespace Ytosk

open T

/-- The remaining last-column frame fields of the dropped matrix. These are
conditions on its own frame, rather than global `AbsD`, `TPLo`, or `AbsUW`. -/
structure TakeFrameV2 (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  ads : AbsDS M ρ rk
  aus : AbsUS M ρ rk
  tplos : TPLoS M ρ rk
  tplow : TPLoWs M ρ rk
  auwl : AbsUWL M ρ
  auw0 : AbsUW0 M ρ rk
  adw : AbsDWs M ρ rk
  trigs : TrigS0 M ρ rk
  tplon : TPLoN M ρ
  adn : AbsDN M ρ

/-- Assemble the one-column drop using the redesigned invariant. Neither the
input nor the result contains the four false global fields of `Inv3V`. -/
theorem inv3V2_take {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (S : SInv M) (I : Inv3V2 M ρ rk) (hl : 2 ≤ M.length)
    (R : DropRes M (M.length - 1) ρ (drop1 M (M.length - 1) rk))
    (F : TakeFrameV2 (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) rk)
    (hTP : TP1LeafG (M.take (M.length - 1)) (drop1 M (M.length - 1) rk))
    (hTPW : TP1WLeafG (M.take (M.length - 1)) (drop1 M (M.length - 1) rk))
    (hRP0 : entry M 0 (M.length - 1) = 0 →
      RootP (M.take (M.length - 1)) (drop1 M (M.length - 1) rk)) :
    Inv3V2 (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) rk := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have VI : ValInv M ρ := ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩
  have V := valInv_drop1 hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.rank VI R
  have hdrop := drop_all hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1
    I.vs R.vst I.fc I.fo R.argT
    (bump_drop hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1
      I.kd I.td R.ab R.ws) R.ua
  have hPH := G.ph3c_drop1 hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab
    I.cons I.rank I.good hdrop I.ph
  have hFC := G.fc3_drop1 hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab
    I.cons I.rank I.good hdrop I.fc3
  have hVA := vsmallRAll_take hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab
    I.cons I.good hC1 hRk1 hdrop I.vra
  have hRP : RootP (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) := by
    by_cases h0 : entry M 0 (M.length - 1) = 0
    · exact hRP0 h0
    · exact rootP_drop1 hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r01 S.r12 S.e00
        h0 I.cons I.rank VI R I.rootP
  exact ⟨hC1, V.g, hRk1, V.vs, V.fc, V.fo, V.kd, V.td, hPH, hFC, hVA,
    F.ads, F.aus, tp1C_of_ph3cG hC1 V.g.toOT hPH hTP, F.tplos,
    tp1WC_of_ph3cG hC1 V.g.toOT hPH hTPW, F.tplow, F.auwl, F.auw0,
    F.adw, F.trigs, F.tplon, F.adn, rootS_of_good hC1 V.g, hRP⟩

/-- **`inv3V2_take` from the conclusion of the drop lemma** (2026-10-25): `PO ∧ PV` at every column and
`VSmallNew` in place of `DropRes`. -/
theorem inv3V2_takeD {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (S : SInv M) (I : Inv3V2 M ρ rk) (hl : 2 ≤ M.length)
    (hdrop : ∀ i, i < M.length - 1 → PO ρ (drop1 M (M.length - 1) rk) i ∧
      PV M ρ (drop1 M (M.length - 1) rk) i)
    (hvst : VSmallNew M (M.length - 1) ρ (drop1 M (M.length - 1) rk))
    (F : TakeFrameV2 (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) rk)
    (hTP : TP1LeafG (M.take (M.length - 1)) (drop1 M (M.length - 1) rk))
    (hTPW : TP1WLeafG (M.take (M.length - 1)) (drop1 M (M.length - 1) rk))
    (hRP0 : entry M 0 (M.length - 1) = 0 →
      RootP (M.take (M.length - 1)) (drop1 M (M.length - 1) rk)) :
    Inv3V2 (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) rk := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have VI : ValInv M ρ := ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩
  have V := drop_presD hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons VI hdrop hvst hC1 hRk1
  have hPH := G.ph3c_drop1 hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab
    I.cons I.rank I.good hdrop I.ph
  have hFC := G.fc3_drop1 hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab
    I.cons I.rank I.good hdrop I.fc3
  have hVA := vsmallRAll_take hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab
    I.cons I.good hC1 hRk1 hdrop I.vra
  have hRP : RootP (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) := by
    by_cases h0 : entry M 0 (M.length - 1) = 0
    · exact hRP0 h0
    · exact rootP_take hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r01 S.r12 S.e00 h0 I.cons I.good hC1 hRk1
        (fun i hi => (hdrop i hi).1.le) I.rootP
  exact ⟨hC1, V.g, hRk1, V.vs, V.fc, V.fo, V.kd, V.td, hPH, hFC, hVA,
    F.ads, F.aus, tp1C_of_ph3cG hC1 V.g.toOT hPH hTP, F.tplos,
    tp1WC_of_ph3cG hC1 V.g.toOT hPH hTPW, F.tplow, F.auwl, F.auw0,
    F.adw, F.trigs, F.tplon, F.adn, rootS_of_good hC1 V.g, hRP⟩

end Ytosk
