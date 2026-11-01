/-
The translation-facing top with the repaired invariant.
This does not discharge the three expansion-engine outputs or the drop/frame producers.
The conclusion is order preservation and surjectivity, rather than termination.
-/
import Ytosk.V3MainV3
import Ytosk.V3DropV3

namespace Ytosk.V3Main
open T WfExQ2

/-- Repaired drop inputs and repaired frame fields suffice for the induction core. -/
theorem desc3_of_inputs (hD : HDropInputsV3) (hF : HFrameV3)
    (h0 : ExpOutV3 0) (h1 : ExpOutV3 1) (h2 : ExpOutV3 2) : Desc3 :=
  desc3_V3 (hDropV3_of_inputs hD) hF h0 h1 h2

/-- The values of all nonempty standard matrices below SRO are standard terms. -/
theorem standard_values_V3 (hD : HDropInputsV3) (hF : HFrameV3)
    (h0 : ExpOutV3 0) (h1 : ExpOutV3 1) (h2 : ExpOutV3 2)
    {M : Mat} (hM : Std M) (hS : M ≠ SRO) (hE : M ≠ []) :
    ∃ t, Val M t ∧ isOT t = true := by
  obtain ⟨ρ, rk, I⟩ := inv3V3_all (hDropV3_of_inputs hD) hF h0 h1 h2 M hM hS hE
  exact ⟨_, ⟨ρ, rk, I.cons, I.rank, rfl⟩, root_ot I.good⟩

/-- Order preservation below SRO. The new drop producer replaces the false HDropU. -/
theorem translation_order_V3 (hD : HDropInputsV3) (hF : HFrameV3)
    (h0 : ExpOutV3 0) (h1 : ExpOutV3 1) (h2 : ExpOutV3 2)
    {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA :=
  order_pres (desc3_of_inputs hD hF h0 h1 h2) hA hB hAS hBE hlt

/-- Surjectivity, with the measured EvalFSNZ 2 obligation of WfCof. -/
theorem translation_surj_V3 (hD : HDropInputsV3) (hF : HFrameV3)
    (h0 : ExpOutV3 0) (h1 : ExpOutV3 1) (h2 : ExpOutV3 2) (hFS : EvalFSNZ 2)
    {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  surj_of_evalFSNZ (desc3_of_inputs hD hF h0 h1 h2) hFS hot hvN hlt

end Ytosk.V3Main
