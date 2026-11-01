/-
The one-column drop on the repaired invariant Inv3V3.
No existence or preservation theorem for the refuted Inv3V2 is used.
The remaining drop hypothesis is the measured PO/PV2 conclusion and VSmallNew;
the frame/leaf hypothesis is WfExQ2.HFrameV3.
-/
import Ytosk.WfExQ2
import Ytosk.WfDrL4

namespace Ytosk.V3Main
open T WfExQ1 WfExQ2

/-- The new drop conclusion, including Bad2. This does not assert old PV. -/
def DropV3 (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop :=
  (∀ i, i < M.length - 1 → PO ρ (drop1 M (M.length - 1) rk) i ∧
    PV2 M ρ (drop1 M (M.length - 1) rk) i) ∧
  VSmallNew M (M.length - 1) ρ (drop1 M (M.length - 1) rk)

/-- Producer still to be supplied from the repaired drop inputs. -/
def HDropV3 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3V3 M ρ rk → DropV3 M ρ rk

/-- All carried take fields use only the unchanged part of Inv3V3. -/
theorem take_inv {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (S : SInv M) (I : Inv3V3 M ρ rk) (hl : 2 ≤ M.length)
    (D : DropV3 M ρ rk)
    (F : FrameV3 (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) rk)
    (hTP : TP1LeafG (M.take (M.length - 1)) (drop1 M (M.length - 1) rk))
    (hTPW : TP1WLeafG (M.take (M.length - 1)) (drop1 M (M.length - 1) rk)) :
    Inv3V3 (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) rk := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  have hR : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC := cons_of_rk hR
  have V := drop_presD2 hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons
    (show ValInv M ρ from ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩) D.1 D.2 hC hR
  have hPH := G.ph3c_drop12 hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab
    I.cons I.rank I.good D.1 I.ph
  have hFC := G.fc3_drop12 hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab
    I.cons I.rank I.good D.1 I.fc3
  have hVA := vsmallRAll_take2 hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab
    I.cons I.good hC hR D.1 I.vra
  have hRP : RootP (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) := by
    by_cases h0 : entry M 0 (M.length - 1) = 0
    · have h1 := S.r01 _ h0
      have h2 := S.r12 _ h1
      have hz := (col_zero_iff M (M.length - 1)).mpr ⟨h0, h1, h2⟩
      exact rootP_take_root hx hz I.cons hC hR I.rootP
    · exact rootP_take hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r01 S.r12 S.e00 h0
        I.cons I.good hC hR (fun i hi => (D.1 i hi).1.le) I.rootP
  exact inv3V3_of_parts hC V.g hR (rootS_of_good hC V.g) hRP
    ⟨V.vs, V.fc, V.fo, V.kd, V.td, hPH, hFC, hVA⟩ F hTP hTPW

/-- Strict root decrease on every nontrivial last drop, using PO/PV2 only. -/
theorem take_root_lt {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (S : SInv M) (I : Inv3V3 M ρ rk) (hl : 2 ≤ M.length) (D : DropV3 M ρ rk) :
    root (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) < root M ρ := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  have hR : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC := cons_of_rk hR
  refine (root_take_lt hx S.r01 S.r12 S.e00 I.cons I.good (fun i hi => (D.1 i hi).1.2.1)
    (fun i hi => (D.1 i hi).1.le) ?_).2
  intro R hR' hRA _
  exact path_strict2 hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC hR D.1
    S.r12 S.bumpE2 (M.length - 1 - R) R (M.length - 1) (Nat.le_refl _) (le_refl _) hRA
    (fun h => absurd h (lt_irrefl _)) (fun h => absurd h (lt_irrefl _))
    (fun t _ htx => not_anc_out (by omega) (by have := htx.le; omega))
    (fun e he hxe => by have := (mem_children he).2; omega) hR'

/-- The last drop, with the original ranking and canonical drop valuation. -/
theorem last_inv (hD : HDropV3) (hF : HFrameV3) {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (hl : 2 ≤ M.length)
    (I : Inv3V3 M ρ rk) :
    Inv3V3 (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) rk := by
  have S := sInv_std hM hS
  have D := hD M ρ rk hM hS hl I
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  have hR : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC := cons_of_rk hR
  have hG := good3_take2 hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC hR D.1
  obtain ⟨F, hTP, hTPW⟩ := hF _ _ rk (std_take hM _ (by omega)) (ne_SRO_of_rk hR)
    (take_ne_nil_of (by omega) (by omega)) hC hR hG
  exact take_inv S I hl D F hTP hTPW

/-- Every nonempty proper prefix carries Inv3V3 with the same ranking. -/
theorem prefix_inv (hD : HDropV3) (hF : HFrameV3) {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3V3 M ρ rk) :
    ∀ j, 1 ≤ j → j < M.length → Inv3V3 (M.take j) (drop1 M j rk) rk := by
  have key : ∀ m j, 1 ≤ j → j + 1 + m = M.length → Inv3V3 (M.take j) (drop1 M j rk) rk := by
    intro m
    induction m with
    | zero =>
      intro j hj hm
      have h := last_inv hD hF hM hS (by omega) I
      rwa [show M.length - 1 = j from by omega] at h
    | succ m ih =>
      intro j hj hm
      have I1 := ih (j + 1) (by omega) (by omega)
      have hl1 : (M.take (j + 1)).length = j + 1 := by rw [List.length_take]; omega
      have h := last_inv hD hF (std_take hM (j + 1) (by omega)) (ne_SRO_of_rk I1.rank)
        (by omega) I1
      rw [hl1, show j + 1 - 1 = j from by omega, take_take_succ, drop1_take_succ] at h
      exact h
  intro j hj hjl
  exact key (M.length - 1 - j) j hj (by omega)

end Ytosk.V3Main
