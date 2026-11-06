/-
**The translation below SRO from the current residuals (2026-11-06).**

`V3TranslationAllUV3` takes 11 inputs.  Here the inputs hD, hFO, hSF, hSP and hN are replaced by their reductions:
- hD ⟸ `HDropInputsV3` (`hDropV3_of_inputs`);
- hFO ⟸ `T2C2RootRel` at the C2 configurations (`hFO_of_C2rel`);
- hSF, hSP ⟸ `HCanon`, `SeedPFResV3R3`, `C2Kids`, `T2C2RootRel` (`hSF_of4`, `hSP_of4`);
- hN ⟸ `HCanon`, `hBXU`, `SeedVFResV3R3` (contains `SeedPFResV3R3`), `FDshAt`, `C2Kids`, `T2VRAQNDom`, `T2VRASeedC`,
  `T2VRACopyEsc2`, `VDomU`, `KAG2` (`hN_of8`).
The other inputs (hF, hAbsU, hSeeds, hQR, hQN, hBXU) are unchanged.
-/
import Ytosk.V3TranslationAllUV3
import Ytosk.V3SeedCanon

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G

section
variable (hDI : HDropInputsV3) (hF : HFrameV3)
    (hAbsU : T0AtV3 (fun M ρ r L => T0AbsWU M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ))
    (hQR : HQRInputsStepV3) (hQN : HQNInputsV3)
    (hBXU : T2AtV3 T2BelowAtV3U)
    (hCan : HCanon)
    (hVF : T2AtV3 (fun M ρ => SeedVFResV3R3 M ρ))
    (hK : T2AtV3 (fun M ρ => C2Kids M ρ))
    (hC2R : T2AtV3 (fun M ρ => ∀ r L q k,
      r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFO.T2C2RootRel M ρ r L q))
    (hFD : T2AtV3 (fun M _ => T2CopyK FDshAt M))
    (hQNd : T2AtV3 (fun M ρ => ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r →
      par M 0 (r + L) = some q → q ≠ r → ∀ Lc, CL M r = Lc ++ [q] → T2VRAQNDom M ρ r L q Lc))
    (hSC : T2AtV3 (fun M _ => T2VRASeedC M))
    (hCopy : T2AtV3 (fun M _ => T2VRACopyEsc2 M))
    (hVD : T2AtV3 (fun M _ => T2VRAK (fun V V' a Lv _ u => VDomU V V' a Lv u) M))
    (hAG : T2AtV3 (fun M _ => T2VRAK KAG2 M))

include hDI hF hAbsU hSeeds hQR hQN hBXU hCan hVF hK hC2R hFD hQNd hSC hCopy hVD hAG

theorem desc3_res : Desc3 :=
  desc3_of_step_enginesV3UU (hDropV3_of_inputs hDI) hF hAbsU hSeeds hQR hQN hBXU
    (SeedFO.hFO_of_C2rel hC2R)
    (hSF_of4 hCan (fun M ρ rk C hz h2 => (hVF M ρ rk C hz h2).pf) hK hC2R)
    (hSP_of4 hCan (fun M ρ rk C hz h2 => (hVF M ρ rk C hz h2).pf) hK hC2R)
    (hN_of8 hCan hBXU hVF hFD hK hQNd hSC hCopy hVD hAG)

/-- **Order preservation of the translation below SRO** from the current residuals. -/
theorem translation_order_res
    {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA :=
  order_pres (desc3_res hDI hF hAbsU hSeeds hQR hQN hBXU hCan hVF hK hC2R hFD hQNd hSC hCopy hVD hAG)
    hA hB hAS hBE hlt

/-- **Surjectivity of the translation below SRO** from the current residuals and `EvalFSNZ 2`. -/
theorem translation_surj_res (hFS : EvalFSNZ 2)
    {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  surj_of_evalFSNZ (desc3_res hDI hF hAbsU hSeeds hQR hQN hBXU hCan hVF hK hC2R hFD hQNd hSC hCopy hVD hAG)
    hFS hot hvN hlt

end

#print axioms translation_order_res
#print axioms translation_surj_res

end Ytosk.V3Main.SeedPF
