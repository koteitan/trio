/-
**t = 2, qn: the second field of `T2SeedQNDom` is `T2VRAQNDom` at the level `V` (2026-11-07).**

At `u = V` (a level of `r`, `LevAt`), `comps V V = []`, so `T2VRAQNDom` gives: the components of `s'` at the level `V` are
below `Ω_{s'}` or `B`.  `T2SeedQNDomF` keeps the first field.
-/
import Ytosk.V3RwFree

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- The first field of `T2SeedQNDom`. -/
def T2SeedQNDomF (M : Mat) (ρ : Valn) (r L q : Nat) (Lc : List Nat) : Prop :=
  Lc ≠ [] → ∀ u, ¬ lt (ρ.v r) u = true → ∀ g ∈ comps u (qnS M ρ r L q),
    g = z ∨ g ≤ t2B (ρ.v r) ρ Lc ∨ g ≤ psi (qnS M ρ r L q) z z ∨
      (∃ d ∈ comps u (t2B (ρ.v r) ρ Lc), g ≤ d) ∨ ∃ d ∈ comps u (ρ.v r), g ≤ d

theorem t2SeedQNDom_ofF {M : Mat} {ρ : Valn} {r L q : Nat} {Lc : List Nat} (hVot : isOT (ρ.v r) = true)
    (hF : T2SeedQNDomF M ρ r L q Lc) (hV : T2VRAQNDom M ρ r L q Lc) : T2SeedQNDom M ρ r L q Lc := by
  refine ⟨hF, fun g hg => ?_⟩
  rcases hV (ρ.v r) (Or.inl rfl) (fun h => lt_irrefl' _ h) g hg with h | h | ⟨d, hd, _⟩
  · exact Or.inl h
  · exact Or.inr h
  · rw [comps_self_nil hVot] at hd; simp at hd

/-- `SeedVFResV3R7` with `T2SeedQNDomF`. -/
structure SeedVFResV3R8 (M : Mat) (ρ : Valn) : Prop where
  pf : SeedPFResV3R7 M ρ
  qnDomF : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → T2SeedQNDomF M ρ r L q Lc
  cDom : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = none → T2SeedCDomR M ρ r L q
  C2r : ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFr QVF M r L r

theorem seedVFResV3R7_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3W M ρ rk) (h : SeedVFResV3R8 M ρ)
    (hQN : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      ∀ Lc, CL M r = Lc ++ [q] → T2VRAQNDom M ρ r L q Lc) : SeedVFResV3R7 M ρ :=
  ⟨h.pf, fun r L q hlen hr hq hqr Lc hLc => t2SeedQNDom_ofF (I.good.ot_v r (by omega))
    (h.qnDomF r L q hlen hr hq hqr Lc hLc) (hQN r L q hlen hr hq hqr Lc hLc), h.cDom, h.C2r⟩

section
variable (hDI : HDropInputsV3) (hF : HFrameV3)
    (hAbsU : T0AtV3 (fun M ρ r L => T0AbsWU M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ))
    (hQR : HQRInputsStepV3) (hQN : HQNInputsV3)
    (hBXU2 : T2AtV3 (fun M ρ => T2BelowAtV3U2 M ρ))
    (hCanH2 : HCanonHard2)
    (hVF8 : T2AtV3 (fun M ρ => SeedVFResV3R8 M ρ))
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

include hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2 hVF8 hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG

/-- **Order preservation of the translation below SRO** from the current residuals (`SeedVFResV3R8`). -/
theorem translation_order_res13
    {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA :=
  translation_order_res12 hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2
    (fun M ρ rk C hz h2 => seedVFResV3R7_of (coreW C.S C.I) (hVF8 M ρ rk C hz h2) (hQNd M ρ rk C hz h2))
    hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG hA hB hAS hBE hlt

/-- **Surjectivity of the translation below SRO** from the current residuals and `EvalFSNZ 2`. -/
theorem translation_surj_res13 (hFS : EvalFSNZ 2)
    {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  translation_surj_res12 hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2
    (fun M ρ rk C hz h2 => seedVFResV3R7_of (coreW C.S C.I) (hVF8 M ρ rk C hz h2) (hQNd M ρ rk C hz h2))
    hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG hFS hot hvN hlt

end

#print axioms translation_order_res13
#print axioms translation_surj_res13

end Ytosk.V3Main.SeedPF
