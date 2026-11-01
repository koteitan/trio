/- Conditional entry points isolating the FStep QR repair and the widened t=2
absorption frame. -/
import Ytosk.V3QRStepV3
import Ytosk.V3TranslationInputsV3
import Ytosk.V3T2CarrierV3U
namespace Ytosk.V3Main
open T WfExQ1 WfExQ2 WfAbsW WfT2X

/-- The old below-boundary input implies the widened upgrade-shape input. -/
theorem T2BelowAtV3.toU {M : Mat} {ρ : Valn} (h : T2BelowAtV3 M ρ) : T2BelowAtV3U M ρ := by
  intro r L hlen hr n hn hGP σ hCN hOT
  rcases h r L hlen hr n hn hGP σ hCN hOT with ⟨hHard, hSeed, hW, hAbs, hNB⟩
  exact ⟨hHard, hSeed, hW, AbsWNx.toU hAbs, notBumpKidXU_of hNB⟩

/-- The t=2 output using the widened AbsWNxU frame residual. -/
theorem expOut2_of_inputsU (hF : HFrameV3)
    (hBXU : T2AtV3 T2BelowAtV3U)
    (hFO : T2AtV3 (fun M _ => T2SeedFrames QFO M))
    (hSF : T2AtV3 (fun M _ => T2SeedFrames G.QT2F M))
    (hSP : T2AtV3 (fun M _ => T2SeedFrames G.QT2P M))
    (hN : T2SmallV3) : ExpOutV3 2 := by
  intro M ρ rk C hz h2
  have hl : 2 ≤ M.length := by
    obtain ⟨r, hr⟩ := parLast_of C.S.e00 C.S.r01 C.S.r12 hz
    rw [h2] at hr
    have := par_lt M 2 _ r hr
    omega
  have I1 := C.pre (M.length - 1) (by omega) (by omega)
  intro n hn
  obtain ⟨σ, rkN, IN, _, hlt⟩ :=
    t2_carrierV3U hF (hBXU M ρ rk C hz h2) C.std C.ne C.I (C.drop hl) I1 hz h2
      (hFO M ρ rk C hz h2) (hSF M ρ rk C hz h2) (hSP M ρ rk C hz h2)
      (hN M ρ rk C hz h2) n hn
  exact ⟨σ, rkN, IN, hlt⟩

section
variable (hD : HDropV3) (hF : HFrameV3)
    (hAbs : T0AtV3 (fun M ρ r L => T0AbsW M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ))
    (hQR : HQRInputsStepV3) (hQN : HQNInputsV3)
    (hBXU : T2AtV3 T2BelowAtV3U)
    (hFO : T2AtV3 (fun M _ => T2SeedFrames QFO M))
    (hSF : T2AtV3 (fun M _ => T2SeedFrames G.QT2F M))
    (hSP : T2AtV3 (fun M _ => T2SeedFrames G.QT2P M))
    (hN : T2SmallV3)

include hD hF hAbs hSeeds hQR hQN hBXU hFO hSF hSP hN

theorem desc3_of_step_enginesV3U : Desc3 :=
  desc3_V3 hD hF (expOutV3_of_core hF (expCore0_of_seeds hAbs hSeeds))
    (expOut1_of_step_inputs hF hQR hQN) (expOut2_of_inputsU hF hBXU hFO hSF hSP hN)

/-- Order preservation of the translation below SRO, conditional on the listed inputs. -/
theorem translation_order_of_step_enginesV3U
    {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA :=
  order_pres (desc3_of_step_enginesV3U hD hF hAbs hSeeds hQR hQN hBXU hFO hSF hSP hN)
    hA hB hAS hBE hlt

/-- Surjectivity additionally needs the existing EvalFSNZ 2 cofinality obligation. -/
theorem translation_surj_of_step_enginesV3U (hFS : EvalFSNZ 2)
    {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  surj_of_evalFSNZ (desc3_of_step_enginesV3U hD hF hAbs hSeeds hQR hQN hBXU hFO hSF hSP hN)
    hFS hot hvN hlt

end

end Ytosk.V3Main
