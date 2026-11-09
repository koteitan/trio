/-
**t = 2, C1: the strict field of `CRelR2` holds (2026-11-10).**

`c1_strict_of_rules` (V3C1Src: the flow from the source `q`) with the value rules for a general `V'`
(V3FlowRulesG, codex: `v_upg_takeG`, `ruleC_G`, `ruleB_G`, `ruleNR_G`) at `V' = qnS`. The C1 field of the seed
residuals keeps only `decP`: `SeedPFResV3R9`, `SeedVFResV3R11`, `translation_order_res16`.
-/
import Ytosk.V3FlowRulesG
import Ytosk.V3C1Src

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **`X₁ < σ_{V,qnS}(X₁)` in the C1 case.** -/
theorem c1_strict_holds {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q])
    (hun : upg M (r + L - 1) = none) :
    ∀ τ, Cons (M.take (r + L)) τ → t2X1 M r L τ < sh (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) := by
  intro τ hτ
  have hx : r + L + 1 = M.length := hlen
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hrM : r < M.length := by omega
  have hx1 : M.length - 1 = r + L := by omega
  have hτ' : Cons (M.take (M.length - 1)) τ := by rw [hx1]; exact hτ
  have hG := good3_take_anyV3U I (Ctx.drop (by omega)) (by omega) hτ'
  rw [hx1] at hG
  have hRk : Rk (M.take (r + L)) rk := rk_take_all I.rank I.r0p I.z2 I.sd I.z1 I.uab (r + L) (by omega)
  have hvr : τ.v r = ρ.v r := v_take_of_untopped I hlen (by omega) (topP_C hM hS I hlen hr hq hqr) hτ
  have hux : ∀ c, upg M (r + L - 1) = some c → c = r + L := by
    intro c hc; rw [hun] at hc; cases hc
  have hV : isOT (ρ.v r) = true := I.good.ot_v r hrM
  have hW : isOT (qnS M ρ r L q) = true := qnS_ot I hrM L q
  have hVW : ρ.v r < qnS M ρ r L q := qnS_gt M ρ r L q
  exact c1_strict_of_rules hM hS I hlen hr hq hqr hncl hun hτ
    (fun i j hu hjx _ hSV => by rw [v_upg_takeG I hx hτ hG hux hu hjx]; exact hSV)
    (ruleC_G I hx hτ hG hRk hrx hV hW hVW hvr)
    (ruleB_G I hx hτ hG hRk hrx hq hV hW hVW hvr)
    (ruleNR_G I hx hτ hG hRk hux hrx hvr)

#print axioms c1_strict_holds

/-- `SeedPFResV3R8` with the C1 field reduced to `decP`. -/
structure SeedPFResV3R9 (M : Mat) (ρ : Valn) : Prop where
  qr : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    (∀ i, upg M i ≠ some (r + L)) → ∀ Lc, CL M r = Lc ++ [r + L] → QRNoSwitch M ρ r L Lc
  C1d : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = none →
    ∀ τ, Cons (M.take (r + L)) τ → ∀ Lc c0, CL (M.take (r + L)) r = Lc ++ [c0] →
      ∃ s y, τ.o c0 = psi s y z ∧ qnS M ρ r L q < s
  C2r : ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFr QPF M r L r

theorem seedPFResV3R8_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk) (h : SeedPFResV3R9 M ρ) : SeedPFResV3R8 M ρ :=
  ⟨h.qr, fun r L q hlen hr hq hqr hncl hun =>
    ⟨h.C1d r L q hlen hr hq hqr hncl hun, c1_strict_holds hM hS I Ctx hlen hr hq hqr hncl hun⟩, h.C2r⟩

/-- `SeedVFResV3R10` with `SeedPFResV3R9`. -/
structure SeedVFResV3R11 (M : Mat) (ρ : Valn) : Prop where
  pf : SeedPFResV3R9 M ρ
  qnDomF : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → T2SeedQNDomF M ρ r L q Lc
  C2r : ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFr QVF M r L r

theorem seedVFResV3R10_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk) (h : SeedVFResV3R11 M ρ) : SeedVFResV3R10 M ρ :=
  ⟨seedPFResV3R8_of hM hS I Ctx h.pf, h.qnDomF, h.C2r⟩

section
variable (hDI : HDropInputsV3) (hF : HFrameV3)
    (hAbsU : T0AtV3 (fun M ρ r L => T0AbsWU M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ))
    (hQR : HQRInputsStepV3) (hQN : HQNInputsV3)
    (hBXU2 : T2AtV3 (fun M ρ => T2BelowAtV3U2 M ρ))
    (hCanH2 : HCanonHard2)
    (hVF11 : T2AtV3 (fun M ρ => SeedVFResV3R11 M ρ))
    (hK5 : T2AtV3 (fun M ρ => C2Kids5 M ρ))
    (hC2R4 : T2AtV3 (fun M ρ => ∀ r L q k,
      r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → T2C2RootRel4 M ρ r L q))
    (hFD : T2AtV3 (fun M _ => T2CopyK FDshAt M))
    (hQNd : T2AtV3 (fun M ρ => ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r →
      par M 0 (r + L) = some q → q ≠ r → ∀ Lc, CL M r = Lc ++ [q] → T2VRAQNDom M ρ r L q Lc))
    (hSC : T2AtV3 (fun M _ => T2VRASeedC M))
    (hCopy : T2AtV3 (fun M _ => T2VRACopyEsc2 M))
    (hVD : T2AtV3 (fun M _ => T2VRAK (fun V V' a Lv _ u => VDomU V V' a Lv u) M))
    (hAG : T2AtV3 (fun M _ => T2VRAK KAG2 M))

include hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2 hVF11 hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG

/-- **Order preservation of the translation below SRO** from the current residuals (`SeedVFResV3R11`). -/
theorem translation_order_res16
    {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA :=
  translation_order_res15 hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2
    (fun M ρ rk C hz h2 => seedVFResV3R10_of C.std C.ne (coreW C.S C.I) C (hVF11 M ρ rk C hz h2))
    hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG hA hB hAS hBE hlt

/-- **Surjectivity of the translation below SRO** from the current residuals and `EvalFSNZ 2`. -/
theorem translation_surj_res16 (hFS : EvalFSNZ 2)
    {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  translation_surj_res15 hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2
    (fun M ρ rk C hz h2 => seedVFResV3R10_of C.std C.ne (coreW C.S C.I) C (hVF11 M ρ rk C hz h2))
    hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG hFS hot hvN hlt

end

#print axioms translation_order_res16
#print axioms translation_surj_res16

end Ytosk.V3Main.SeedPF
