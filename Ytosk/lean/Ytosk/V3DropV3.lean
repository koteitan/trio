/-
The repaired drop producer for Inv3V3.
Its inputs are the new WCS2/BumpAbsCB2 conditions, never the false HDropU/PV.
The input fields remain explicit proof obligations; no consistency theorem is claimed.
-/
import Ytosk.V3TakeV3
import Ytosk.WfSdP2

namespace Ytosk.V3Main
open T WfExQ1

/-- Inputs of the already verified repaired drop lemma, at the canonical last drop. -/
structure DropInputsV3 (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  hard : HardArg M (M.length - 1) ρ (drop1 M (M.length - 1) rk)
  vst : VSmallNew M (M.length - 1) ρ (drop1 M (M.length - 1) rk)
  ws : BumpWeakSrcB2 M (M.length - 1) ρ (drop1 M (M.length - 1) rk)
  ab : BumpAbsCB2 M (M.length - 1) ρ
  ua : ∀ i k W, i + 1 = M.length - 1 → upg M i = some k →
    ρ.v k = add (vOpt ρ (par M 1 i)) W → W ≠ z →
      (∀ q ∈ summands (vOpt ρ (par M 1 i)), q < W → Lhd z q W) ∨
        WCSP2 M ρ i (add (vOpt ρ (par M 1 i)) one)

/-- A producer for the five repaired drop inputs, with Inv3V3 as its source bundle. -/
def HDropInputsV3 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3V3 M ρ rk → DropInputsV3 M ρ rk

/-- The new drop theorem applies using only retained fields of Inv3V3. -/
theorem dropV3_of_inputs {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (S : SInv M) (I : Inv3V3 M ρ rk) (hl : 2 ≤ M.length) (R : DropInputsV3 M ρ rk) :
    DropV3 M ρ rk := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  have hR : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  exact ⟨drop_all_hardW2B hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good
    (cons_of_rk hR) hR I.vs R.vst I.fc I.fo R.hard I.kd I.td R.ab R.ws R.ua, R.vst⟩

theorem hDropV3_of_inputs (h : HDropInputsV3) : HDropV3 :=
  fun M ρ rk hM hS hl I => dropV3_of_inputs (sInv_std hM hS) I hl (h M ρ rk hM hS hl I)

end Ytosk.V3Main
