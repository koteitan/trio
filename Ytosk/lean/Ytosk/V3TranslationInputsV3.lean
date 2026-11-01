/-
Translation-facing assembly of the repaired t=0, t=1 and t=2 engines.
All hypotheses remain explicit proof obligations: this is not a proof that the
remaining hypotheses hold for every standard matrix. In particular the records
for local engine inputs do not reduce the number of mathematical obligations.
The old inconsistent Inv3V2 top is neither invoked nor changed.
-/
import Ytosk.V3T0CarrierV3
import Ytosk.V3T1V3
import Ytosk.V3T2CarrierV3

namespace Ytosk.V3Main
open T WfExQ1 WfExQ2

/-- A source-side t=2 obligation at its actual StepCtx3 frame. -/
def T2AtV3 (P : Mat → Valn → Prop) : Prop :=
  ∀ M ρ rk, StepCtx3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 → P M ρ

/-- Only the three unassembled target fields of the t=2 carrier.
Good3, root descent and the other five carried fields are proved by the engine. -/
def T2SmallV3 : Prop :=
  ∀ M ρ rk, StepCtx3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 → ∀ n, 2 ≤ n → ∀ σ rkN,
    Cons (expand M n) σ → Rk (expand M n) rkN → Good3 (expand M n) σ →
    PH3cG (expand M n) σ → VSmallF (expand M n) σ ∧
      FrameClosed (expand M n) σ ∧ VSmallRAll (expand M n) σ

theorem expOut2_of_inputs (hF : HFrameV3)
    (hBX : T2AtV3 T2BelowAtV3)
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
    t2_carrierV3 hF (hBX M ρ rk C hz h2) C.std C.ne C.I (C.drop hl) I1 hz h2
      (hFO M ρ rk C hz h2) (hSF M ρ rk C hz h2) (hSP M ρ rk C hz h2)
      (hN M ρ rk C hz h2) n hn
  exact ⟨σ, rkN, IN, hlt⟩

section
variable (hD : HDropInputsV3) (hF : HFrameV3)
    (hAbs : T0AtV3 (fun M ρ r L => T0AbsW M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ))
    (hQR : HQRInputsV3) (hQN : HQNInputsV3)
    (hBX : T2AtV3 T2BelowAtV3)
    (hFO : T2AtV3 (fun M _ => T2SeedFrames QFO M))
    (hSF : T2AtV3 (fun M _ => T2SeedFrames G.QT2F M))
    (hSP : T2AtV3 (fun M _ => T2SeedFrames G.QT2P M))
    (hN : T2SmallV3)

include hD hF hAbs hSeeds hQR hQN hBX hFO hSF hSP hN

/-- The repaired induction with the three actual expansion engines connected. -/
theorem desc3_of_enginesV3 : Desc3 :=
  desc3_of_inputs hD hF (expOutV3_of_core hF (expCore0_of_seeds hAbs hSeeds))
    (expOut1_of_inputs hF hQR hQN) (expOut2_of_inputs hF hBX hFO hSF hSP hN)

/-- Order preservation of the translation below SRO, conditional on the listed inputs. -/
theorem translation_order_of_enginesV3
    {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA :=
  order_pres (desc3_of_enginesV3 hD hF hAbs hSeeds hQR hQN hBX hFO hSF hSP hN)
    hA hB hAS hBE hlt

/-- Surjectivity additionally needs the existing EvalFSNZ 2 cofinality obligation. -/
theorem translation_surj_of_enginesV3 (hFS : EvalFSNZ 2)
    {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  surj_of_evalFSNZ (desc3_of_enginesV3 hD hF hAbs hSeeds hQR hQN hBX hFO hSF hSP hN)
    hFS hot hvN hlt

end
end Ytosk.V3Main
