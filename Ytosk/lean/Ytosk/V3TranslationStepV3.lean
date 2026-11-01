/- Conditional entry points isolating the FStep QR repair.
This does not claim a consistent global input bundle: the separate t0/t2
absorption inputs remain refuted and must be repaired before adoption. -/
import Ytosk.V3QRStepV3
import Ytosk.V3TranslationInputsV3
namespace Ytosk.V3Main
open T WfExQ1 WfExQ2
section
variable (hD : HDropV3) (hF : HFrameV3)
    (hAbs : T0AtV3 (fun M ρ r L => T0AbsW M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ))
    (hQR : HQRInputsStepV3) (hQN : HQNInputsV3)
    (hBX : T2AtV3 T2BelowAtV3)
    (hFO : T2AtV3 (fun M _ => T2SeedFrames QFO M))
    (hSF : T2AtV3 (fun M _ => T2SeedFrames G.QT2F M))
    (hSP : T2AtV3 (fun M _ => T2SeedFrames G.QT2P M))
    (hN : T2SmallV3)

include hD hF hAbs hSeeds hQR hQN hBX hFO hSF hSP hN

theorem desc3_of_step_enginesV3 : Desc3 :=
  desc3_V3 hD hF (expOutV3_of_core hF (expCore0_of_seeds hAbs hSeeds))
    (expOut1_of_step_inputs hF hQR hQN) (expOut2_of_inputs hF hBX hFO hSF hSP hN)

/-- Order preservation of the translation below SRO, conditional on the listed inputs. -/
theorem translation_order_of_step_enginesV3
    {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA :=
  order_pres (desc3_of_step_enginesV3 hD hF hAbs hSeeds hQR hQN hBX hFO hSF hSP hN)
    hA hB hAS hBE hlt

/-- Surjectivity additionally needs the existing EvalFSNZ 2 cofinality obligation. -/
theorem translation_surj_of_step_enginesV3 (hFS : EvalFSNZ 2)
    {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  surj_of_evalFSNZ (desc3_of_step_enginesV3 hD hF hAbs hSeeds hQR hQN hBX hFO hSF hSP hN)
    hFS hot hvN hlt

end

end Ytosk.V3Main
