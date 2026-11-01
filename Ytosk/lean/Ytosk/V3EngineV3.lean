/-
Engine-facing interface for the repaired top.
Last-column frame fields are supplied once by HFrameV3, rather than assumed
again in every expansion output. The carried engine fields remain obligations.
-/
import Ytosk.V3TranslationV3

namespace Ytosk.V3Main
open T WfExQ1 WfExQ2

/-- The valid structural/value sub-bundle of the old t=2 engine. -/
theorem coreW {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (S : SInv M) (I : Inv3V3 M ρ rk) : Inv3W M ρ rk :=
  ⟨S.r0p, S.z2, S.sibDec, S.z1c, S.uat, S.uab, S.r12, S.bumpE2, S.r01, S.e00,
    I.cons, I.good, I.rank, I.vs, I.fc, I.fo, I.kd, I.td, I.rootS, I.rootP⟩

/-- The valid structural/value sub-bundle of the old t=0 engine. -/
theorem coreC {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (S : SInv M) (I : Inv3V3 M ρ rk) : Inv3C M ρ rk :=
  ⟨S.r0p, S.z2, S.sibDec, S.z1c, S.uat, S.uab, S.r12, S.bumpE2, S.r01, S.e00,
    I.cons, I.good, I.rank, I.vs, I.fc, I.fo, I.kd, I.td, I.rootS, I.rootP⟩

/-- Positive-index expansions of a matrix of length at least two are nonempty. -/
theorem expand_nonempty {M : Mat} (hl : 2 ≤ M.length) {n : Nat} (hn : 1 ≤ n) :
    expand M n ≠ [] := by
  rcases expand_cases M n hl with he | ⟨r, hr, he⟩
  · rw [he]
    exact take_ne_nil_of (by omega) (by omega)
  · have hrx := par_lt M (TRIO.srow M (M.length - 1)) (M.length - 1) r hr
    rw [he]
    intro h
    have hh := congrArg List.length h
    rw [TRIO.gexp_length (by omega)] at hh
    simp only [List.length_nil] at hh
    have hpos := Nat.mul_pos (show 0 < n from by omega)
      (show 0 < M.length - 1 - r from by omega)
    omega


/-- The unchanged carried part of an engine output. This does not include the
last-column frame fields or either leaf condition. -/
def ExpCoreV3 (t : Nat) : Prop :=
  ∀ M ρ rk, StepCtx3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = t → ∀ n, 2 ≤ n →
      ∃ σ rkN, Cons (expand M n) σ ∧ Rk (expand M n) rkN ∧ Good3 (expand M n) σ ∧
        CarryV3 (expand M n) σ ∧ RootP (expand M n) σ ∧ root (expand M n) σ < root M ρ

/-- A carrier engine and the repaired global frame fields give the full output.
The ranking gives ne-SRO; nonemptiness is structural, not an extra residual. -/
theorem expOutV3_of_core (hF : HFrameV3) {t : Nat} (h : ExpCoreV3 t) : ExpOutV3 t := by
  intro M ρ rk C hz hs n hn
  obtain ⟨σ, rkN, hC, hR, hG, K, hP, hlt⟩ := h M ρ rk C hz hs n hn
  have hl : 2 ≤ M.length := by
    have hpos := List.length_pos_of_ne_nil C.nonempty
    by_contra he
    have hx : M.length - 1 = 0 := by omega
    have h0 : entry M 0 (M.length - 1) = 0 := by simpa only [hx] using C.S.e00
    exact hz ((col_zero_iff M _).mpr ⟨h0, C.S.r01 _ h0, C.S.r12 _ (C.S.r01 _ h0)⟩)
  obtain ⟨F, hTP, hTPW⟩ := hF _ σ rkN (Std.exp n C.std) (ne_SRO_of_rk hR)
    (expand_nonempty hl (by omega)) hC hR hG
  exact ⟨σ, rkN, inv3V3_of_parts hC hG hR (rootS_of_good hC hG) hP K F hTP hTPW, hlt⟩

/-- Repaired invariant induction from the still-open carrier engine outputs. -/
theorem inv3V3_all_of_cores (hD : HDropInputsV3) (hF : HFrameV3)
    (h0 : ExpCoreV3 0) (h1 : ExpCoreV3 1) (h2 : ExpCoreV3 2) :
    ∀ M, Std M → M ≠ SRO → M ≠ [] → ∃ ρ rk, Inv3V3 M ρ rk :=
  inv3V3_all (hDropV3_of_inputs hD) hF
    (expOutV3_of_core hF h0) (expOutV3_of_core hF h1) (expOutV3_of_core hF h2)

theorem desc3_of_cores (hD : HDropInputsV3) (hF : HFrameV3)
    (h0 : ExpCoreV3 0) (h1 : ExpCoreV3 1) (h2 : ExpCoreV3 2) : Desc3 :=
  desc3_of_inputs hD hF (expOutV3_of_core hF h0) (expOutV3_of_core hF h1) (expOutV3_of_core hF h2)

/-- Translation order preservation; expansion engines need only their carried fields. -/
theorem translation_order_of_cores (hD : HDropInputsV3) (hF : HFrameV3)
    (h0 : ExpCoreV3 0) (h1 : ExpCoreV3 1) (h2 : ExpCoreV3 2)
    {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA :=
  order_pres (desc3_of_cores hD hF h0 h1 h2) hA hB hAS hBE hlt

/-- Translation surjectivity with the remaining EvalFSNZ 2 obligation. -/
theorem translation_surj_of_cores (hD : HDropInputsV3) (hF : HFrameV3)
    (h0 : ExpCoreV3 0) (h1 : ExpCoreV3 1) (h2 : ExpCoreV3 2) (hFS : EvalFSNZ 2)
    {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  surj_of_evalFSNZ (desc3_of_cores hD hF h0 h1 h2) hFS hot hvN hlt

end Ytosk.V3Main
