/-
**`HCanonHard` without the case where `b` has no bump child (2026-11-06).**

`v(i) = v(p) + ω^{E(i)}` with `E(i) = Σ (1 :: bump terms of the children of i)` for `i = a, b`
(`canonical_v_le_of_exponents`).  If `b` has no bump child, every bump term of `b` is `0`, so `E(b) = 1 ≤ E(a)`
(`sumN_one_zeros`, `le_sumN_append`).  `HCanonHard2` keeps the case where `a` has children and `b` has a bump child.
-/
import Ytosk.V3C2Shape

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- `CanonHard` when `b` has a bump child. -/
def CanonHard2 (N : Mat) (τ : Valn) : Prop :=
  ∀ p a b, a ∈ children N p → b ∈ children N p → a < b →
    (∀ e ∈ children N p, a < e → b ≤ e) →
    entry N 1 a = entry N 1 p + 1 → entry N 2 a = 1 → par N 1 a = some p →
    entry N 1 b = entry N 1 p + 1 → entry N 2 b = 1 → par N 1 b = some p →
    upg N (a - 1) = some a → topped N a = true →
    upg N (b - 1) ≠ some b → Counted N p b → children N a ≠ [] →
    (∃ j ∈ children N b, col N j = bump N b) → τ.v b ≤ τ.v a

theorem canonHard_of_2 {N : Mat} {τ : Valn} (hC : Cons N τ) (hG : Good3 N τ)
    (h : CanonHard2 N τ) : CanonHard N τ := by
  intro p a b ha hb hab hnext ha1 ha2 hpa hb1 hb2 hpb hup htop hno hcnt hca
  by_cases hbb : ∃ j ∈ children N b, col N j = bump N b
  · exact h p a b ha hb hab hnext ha1 ha2 hpa hb1 hb2 hpb hup htop hno hcnt hca hbb
  have haL := (mem_children ha).2
  have hbL := (mem_children hb).2
  apply SibConsumer.canonical_v_le_of_exponents hC hG haL hbL (by omega) (by omega) (by omega) (by omega) hpa hpb
  have hz : ∀ t ∈ (children N b).map (bumpTerm N τ b), t = z := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
    unfold bumpTerm
    rw [if_neg (fun h => hbb ⟨j, hj, h⟩)]
  rw [sumN_one_zeros hz]
  exact le_sumN_append [one] _ (by simp [isOT_one])
    (fun t ht => by obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG a j)

/-- **Residual: `CanonHard2` of every standard matrix.** -/
def HCanonHard2 : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Rk N rk → Good3 N σ → CanonHard2 N σ

theorem hCanonHard_of_2 (h : HCanonHard2) : HCanonHard :=
  fun N σ rk hN hS hC hR hG => canonHard_of_2 hC hG (h N σ rk hN hS hC hR hG)

#print axioms hCanonHard_of_2

section
variable (hDI : HDropInputsV3) (hF : HFrameV3)
    (hAbsU : T0AtV3 (fun M ρ r L => T0AbsWU M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ))
    (hQR : HQRInputsStepV3) (hQN : HQNInputsV3)
    (hBXU2 : T2AtV3 (fun M ρ => T2BelowAtV3U2 M ρ))
    (hCanH2 : HCanonHard2)
    (hVF : T2AtV3 (fun M ρ => SeedVFResV3R3 M ρ))
    (hK4 : T2AtV3 (fun M ρ => C2Kids4 M ρ))
    (hC2R3 : T2AtV3 (fun M ρ => ∀ r L q k,
      r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → T2C2RootRel3 M ρ r L q))
    (hFD : T2AtV3 (fun M _ => T2CopyK FDshAt M))
    (hQNd : T2AtV3 (fun M ρ => ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r →
      par M 0 (r + L) = some q → q ≠ r → ∀ Lc, CL M r = Lc ++ [q] → T2VRAQNDom M ρ r L q Lc))
    (hSC : T2AtV3 (fun M _ => T2VRASeedC M))
    (hCopy : T2AtV3 (fun M _ => T2VRACopyEsc2 M))
    (hVD : T2AtV3 (fun M _ => T2VRAK (fun V V' a Lv _ u => VDomU V V' a Lv u) M))
    (hAG : T2AtV3 (fun M _ => T2VRAK KAG2 M))

include hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2 hVF hK4 hC2R3 hFD hQNd hSC hCopy hVD hAG

/-- **Order preservation of the translation below SRO** from the current residuals (`HCanonHard2`). -/
theorem translation_order_res6
    {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA :=
  translation_order_res5 hDI hF hAbsU hSeeds hQR hQN hBXU2 (hCanonHard_of_2 hCanH2) hVF hK4 hC2R3 hFD hQNd hSC
    hCopy hVD hAG hA hB hAS hBE hlt

/-- **Surjectivity of the translation below SRO** from the current residuals and `EvalFSNZ 2`. -/
theorem translation_surj_res6 (hFS : EvalFSNZ 2)
    {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  translation_surj_res5 hDI hF hAbsU hSeeds hQR hQN hBXU2 (hCanonHard_of_2 hCanH2) hVF hK4 hC2R3 hFD hQNd hSC
    hCopy hVD hAG hFS hot hvN hlt

end

#print axioms translation_order_res6
#print axioms translation_surj_res6

end Ytosk.V3Main.SeedPF
