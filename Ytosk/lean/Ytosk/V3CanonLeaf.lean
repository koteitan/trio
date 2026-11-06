/-
**`HCanon` without the leaf case (2026-11-06).**

`CanonicalNeed` (V3SibConsumer): at a parent `p`, adjacent children `a < b` with the column `(e0 p + 1, e1 p + 1, 1)`
and `P_1 = p`, `a` upgraded from `a − 1` and topped, `b` counted and not upgraded from `b − 1`: `v(b) ≤ v(a)`.
If `a` has no children, `S1` (`S1_std`) gives `subT b ≤ subT a = [col a]`, so `b` has no children either and
`v(b) = v(p) + ω^1 = v(a)` (the same case of `upgSibV_of_hard`, V3SibV).  `HCanonHard` keeps the case where `a` has
children; entry points `translation_order_res4`, `translation_surj_res4`.
-/
import Ytosk.V3T2BelowNarrow
import Ytosk.V3SibV

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- `CanonicalNeed` when `a` has children. -/
def CanonHard (N : Mat) (τ : Valn) : Prop :=
  ∀ p a b, a ∈ children N p → b ∈ children N p → a < b →
    (∀ e ∈ children N p, a < e → b ≤ e) →
    entry N 1 a = entry N 1 p + 1 → entry N 2 a = 1 → par N 1 a = some p →
    entry N 1 b = entry N 1 p + 1 → entry N 2 b = 1 → par N 1 b = some p →
    upg N (a - 1) = some a → topped N a = true →
    upg N (b - 1) ≠ some b → Counted N p b → children N a ≠ [] → τ.v b ≤ τ.v a

theorem canonicalNeed_of_hard {N : Mat} {τ : Valn} (hX : SInvX N) (hS1 : S1 N) (hC : Cons N τ)
    (h : CanonHard N τ) : SibConsumer.CanonicalNeed N τ := by
  intro p a b ha hb hab hnext ha1 ha2 hpa hb1 hb2 hpb hup htop hno hcnt
  by_cases hca : children N a = []
  swap
  · exact h p a b ha hb hab hnext ha1 ha2 hpa hb1 hb2 hpb hup htop hno hcnt hca
  have hpa0 : par N 0 a = some p := (mem_children_iff.mp ha).2
  have hpb0 : par N 0 b = some p := (mem_children_iff.mp hb).2
  have he0a : entry N 0 a = entry N 0 p + 1 := hX.r0p a p hpa0
  have he0b : entry N 0 b = entry N 0 p + 1 := hX.r0p b p hpb0
  have hcolab : col N b = col N a := by
    rw [entry_col N b, entry_col N a, hb1, hb2, he0b, ha1, ha2, he0a]
  obtain ⟨l1, l2, hsplit⟩ := consec_split (children_sorted N p) ha hb hab
    (fun e he ⟨h1, h2⟩ => by have := hnext e he h1; omega)
  have hS := hS1 p l1 l2 a b hsplit
  have hcb : children N b = [] := by
    by_contra hne
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hne
    have htw := subT_tail_ne hc
    rw [subT_leaf hca] at hS
    unfold subT at hS
    rw [hcolab] at hS
    have h2 := (seqLtB_cons_false hS).2 rfl
    cases htw' : (N.drop (b + 1)).takeWhile (fun q => decide (entry N 0 b < q.1)) with
    | nil => exact htw htw'
    | cons q U => rw [htw'] at h2; simp [seqLtB] at h2
  have haL := (mem_children ha).2
  have hbL := (mem_children hb).2
  have hvb : τ.v b = τ.v a := by
    rw [(hC b hbL).2, (hC a haL).2]; unfold vRhs
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), hpb, hpa, hcb, hca]
    rfl
  exact le_of_eq hvb

/-- **Residual: `CanonHard` of every standard matrix.** -/
def HCanonHard : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Rk N rk → Good3 N σ → CanonHard N σ

theorem hCanon_of_hard (h : HCanonHard) : HCanon := by
  intro N σ rk hN hS hC hR hG
  obtain ⟨hX, _⟩ := sInvXJ_std hN hS
  exact canonicalNeed_of_hard hX (S1_std hN) hC (h N σ rk hN hS hC hR hG)

#print axioms hCanon_of_hard

section
variable (hDI : HDropInputsV3) (hF : HFrameV3)
    (hAbsU : T0AtV3 (fun M ρ r L => T0AbsWU M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ))
    (hQR : HQRInputsStepV3) (hQN : HQNInputsV3)
    (hBXU2 : T2AtV3 (fun M ρ => T2BelowAtV3U2 M ρ))
    (hCanH : HCanonHard)
    (hVF : T2AtV3 (fun M ρ => SeedVFResV3R3 M ρ))
    (hK3 : T2AtV3 (fun M ρ => C2Kids3 M ρ))
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

include hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH hVF hK3 hC2R3 hFD hQNd hSC hCopy hVD hAG

/-- **Order preservation of the translation below SRO** from the current residuals (`HCanonHard`). -/
theorem translation_order_res4
    {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA :=
  translation_order_res3 hDI hF hAbsU hSeeds hQR hQN hBXU2 (hCanon_of_hard hCanH) hVF hK3 hC2R3 hFD hQNd hSC
    hCopy hVD hAG hA hB hAS hBE hlt

/-- **Surjectivity of the translation below SRO** from the current residuals and `EvalFSNZ 2`. -/
theorem translation_surj_res4 (hFS : EvalFSNZ 2)
    {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  translation_surj_res3 hDI hF hAbsU hSeeds hQR hQN hBXU2 (hCanon_of_hard hCanH) hVF hK3 hC2R3 hFD hQNd hSC
    hCopy hVD hAG hFS hot hvN hlt

end

#print axioms translation_order_res4
#print axioms translation_surj_res4

end Ytosk.V3Main.SeedPF
