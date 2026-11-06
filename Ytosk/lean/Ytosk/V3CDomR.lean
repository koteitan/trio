/-
**t = 2, C1: the first field of `T2SeedCDom` is proved (2026-11-06).**

`T2SeedCDom1` holds (`t2SeedCDom1_holds`, V3CDomH: the head subscript of `ω^{W₀}` is at most `V`), and it gives the
first field `prefB s' (f(s'))` (`t2SeedCDom1_pref`).  `T2SeedCDomR` keeps the second field: the components of `s'` at the
level `V` are below `Ω_{s'}` or `X₁`.
-/
import Ytosk.V3QNBase
import Ytosk.V3CDomH

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- The second field of `T2SeedCDom`. -/
def T2SeedCDomR (M : Mat) (ρ : Valn) (r L q : Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ →
    ∀ g ∈ comps (ρ.v r) (qnS M ρ r L q), g ≤ psi (qnS M ρ r L q) z z ∨ g ≤ t2X1 M r L τ

theorem t2SeedCDom_ofR {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (h : T2SeedCDomR M ρ r L q) : T2SeedCDom M ρ r L q :=
  fun τ hτ => ⟨fun _ => t2SeedCDom1_pref (t2SeedCDom1_holds hM hS I hlen hr hq hqr), h τ hτ⟩

/-- `SeedVFResV3R4` with `T2SeedCDomR`. -/
structure SeedVFResV3R5 (M : Mat) (ρ : Valn) : Prop where
  pf : SeedPFResV3R4 M ρ
  qnDom : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → T2SeedQNDom M ρ r L q Lc
  cDom : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = none → T2SeedCDomR M ρ r L q
  C2r : ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFr QVF M r L r

theorem seedVFResV3R4_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (h : SeedVFResV3R5 M ρ) : SeedVFResV3R4 M ρ :=
  ⟨h.pf, h.qnDom, fun r L q hlen hr hq hqr hncl hu =>
    t2SeedCDom_ofR hM hS I hlen hr hq hqr (h.cDom r L q hlen hr hq hqr hncl hu), h.C2r⟩

section
variable (hDI : HDropInputsV3) (hF : HFrameV3)
    (hAbsU : T0AtV3 (fun M ρ r L => T0AbsWU M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ))
    (hQR : HQRInputsStepV3) (hQN : HQNInputsV3)
    (hBXU2 : T2AtV3 (fun M ρ => T2BelowAtV3U2 M ρ))
    (hCanH2 : HCanonHard2)
    (hVF5 : T2AtV3 (fun M ρ => SeedVFResV3R5 M ρ))
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

include hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2 hVF5 hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG

/-- **Order preservation of the translation below SRO** from the current residuals (`SeedVFResV3R5`). -/
theorem translation_order_res10
    {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA :=
  translation_order_res9 hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2
    (fun M ρ rk C hz h2 => seedVFResV3R4_of C.std C.ne (coreW C.S C.I) (hVF5 M ρ rk C hz h2))
    hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG hA hB hAS hBE hlt

/-- **Surjectivity of the translation below SRO** from the current residuals and `EvalFSNZ 2`. -/
theorem translation_surj_res10 (hFS : EvalFSNZ 2)
    {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  translation_surj_res9 hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2
    (fun M ρ rk C hz h2 => seedVFResV3R4_of C.std C.ne (coreW C.S C.I) (hVF5 M ρ rk C hz h2))
    hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG hFS hot hvN hlt

end

#print axioms translation_order_res10
#print axioms translation_surj_res10

end Ytosk.V3Main.SeedPF
