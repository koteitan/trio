/- Translation entry points with the upgrade-aware t=0 and t=2 inputs. -/
import Ytosk.V3TranslationAbsUV3
import Ytosk.V3T0CarrierAbsU

namespace Ytosk.V3Main
open T WfExQ1 WfExQ2 WfAbsW WfT2X

section
variable (hD : HDropV3) (hF : HFrameV3)
    (hAbsU : T0AtV3 (fun M ρ r L => T0AbsWU M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ))
    (hQR : HQRInputsStepV3) (hQN : HQNInputsV3)
    (hBXU : T2AtV3 T2BelowAtV3U)
    (hFO : T2AtV3 (fun M _ => T2SeedFrames QFO M))
    (hSF : T2AtV3 (fun M _ => T2SeedFrames G.QT2F M))
    (hSP : T2AtV3 (fun M _ => T2SeedFrames G.QT2P M))
    (hN : T2SmallV3)

include hD hF hAbsU hSeeds hQR hQN hBXU hFO hSF hSP hN

theorem desc3_of_step_enginesV3UU : Desc3 :=
  desc3_V3 hD hF (expOutV3_of_core hF (expCore0_of_seedsU hAbsU hSeeds))
    (expOut1_of_step_inputs hF hQR hQN) (expOut2_of_inputsU hF hBXU hFO hSF hSP hN)

/-- Order preservation of translation below SRO from the upgrade-aware t=0 and t=2 inputs. -/
theorem translation_order_of_step_enginesV3UU
    {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA :=
  order_pres (desc3_of_step_enginesV3UU hD hF hAbsU hSeeds hQR hQN hBXU hFO hSF hSP hN)
    hA hB hAS hBE hlt

/-- Surjectivity additionally uses the existing EvalFSNZ 2 cofinality obligation. -/
theorem translation_surj_of_step_enginesV3UU (hFS : EvalFSNZ 2)
    {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  surj_of_evalFSNZ (desc3_of_step_enginesV3UU hD hF hAbsU hSeeds hQR hQN hBXU hFO hSF hSP hN)
    hFS hot hvN hlt

end

end Ytosk.V3Main
