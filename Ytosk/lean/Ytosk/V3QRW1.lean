/-
**t = 2, qr: the field `QRRelR.w1` from the no-switch residual (2026-11-07).**

`w1`: `¬ B < σ X`, `B` the state of `r` in `M` before `x`, `X` the state of `r` in `M.take x`, `σ = σ_{V,V+1}`.
`σ B = B` (`tame_sigmaB_std`), so it suffices that `X ≤ B`.  `CL_T(r) = Lc` and the children before the last one `c` keep
their `o` (`frame_take`).  So `X = step V B' (o_T c)` and `B = step V B' (o_M c)`.
- `T` triggers: the argument of `o_T(c)` is not `0`, so `o_M(c)` has the same subscript and a larger argument
  (`t2SVc0'_of_dropV3`); `M` triggers (`trig_mono`) and `H` is monotone (`H_mono`).
- neither triggers: `o_T(c) ≤ o_M(c)` (`PO`) and `add` is monotone.
- `M` triggers and `T` does not: excluded by the residual `QRNoSwitch` (no case in the data).
-/
import Ytosk.V3CDomR

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

theorem spArg_snoc {a : T} {Ls : List T} {s y : T} (hs : ∀ t ∈ Ls ++ [psi s y z], Single t)
    (hp : (Ls ++ [psi s y z]).Pairwise (fun a b => b ≤ a)) :
    spArg a z (sumN (Ls ++ [psi s y z])) = step a (spArg a z (sumN Ls)) s y z := by
  rw [sumN_append_dec hs hp, sumN_singleton (hs _ (by simp)), spArg_app, spArg_single]

/-- **Residual (qr): no switch of the trigger at the last child before `x`.** -/
def QRNoSwitch (M : Mat) (ρ : Valn) (r L : Nat) (Lc : List Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → ∀ L' c s y s' y', Lc = L' ++ [c] → ρ.o c = psi s y z → τ.o c = psi s' y' z →
    (lt (spArg (ρ.v r) z (sumN (L'.map ρ.o))) y = true ∧ lt (psi (ρ.v r) z z) (psi s y z) = true) →
    (lt (spArg (ρ.v r) z (sumN (L'.map ρ.o))) y' = true ∧ lt (psi (ρ.v r) z z) (psi s' y' z) = true)

theorem qr_w1_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (Ctx : StepCtx3 M ρ rk) {r L : Nat} {Lc : List Nat} (hlen : r + L + 1 = M.length)
    (hr : par M 2 (r + L) = some r) (hq : par M 0 (r + L) = some r) (hXu : ∀ i, upg M i ≠ some (r + L))
    (hCL : CL M r = Lc ++ [r + L]) (hNS : QRNoSwitch M ρ r L Lc) :
    ∀ τ, Cons (M.take (r + L)) τ → ¬ t2B (ρ.v r) ρ Lc < t2W1 (M.take (r + L)) (ρ.v r) τ r := by
  intro τ hτ
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hL0 : 0 < L := by omega
  have hrM : r < M.length := by omega
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hx1 : M.length - 1 = r + L := by omega
  -- `Good3` of `τ`, the drop valuation
  have hτ' : Cons (M.take (M.length - 1)) τ := by rw [hx1]; exact hτ
  have hG := good3_take_anyV3U I (Ctx.drop (by omega)) (by omega) hτ'
  rw [hx1] at hG
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [hx1] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1
  -- `CL_T(r) = Lc`
  have hxc : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
  have hsplit := children_split_x hlen hxc
  have hxcnt : Counted M r (r + L) := by
    have : r + L ∈ CL M r := by rw [hCL]; simp
    simpa using (List.mem_filter.mp this).2
  have hCLT : CL (M.take (r + L)) r = Lc := by
    have h1 : CL M r = ((children M r).filter (fun d => decide (d < r + L))).filter
        (fun c => decide (Counted M r c)) ++ [r + L] := by
      unfold CL; conv_lhs => rw [hsplit, List.filter_append]
      simp [hxcnt]
    rw [hCL] at h1
    have h2 := (List.append_inj' h1 rfl).1
    rw [h2]; unfold CL; rw [children_take]
    apply List.filter_congr
    intro d hd
    have hd' := List.mem_filter.mp hd
    have hdx : d < r + L := by simpa using hd'.2
    have hdr : d ≠ r := by have := (mem_children hd'.1).1; omega
    simp only [decide_eq_decide]
    constructor
    · intro h; exact hcnt r d (by omega) (by rw [children_take]; exact hd) h
    · intro h; exact counted_take_of hlen hL0 hq hdx hdr h hrx
  have hVot : isOT (ρ.v r) = true := I.good.ot_v r hrM
  have hVs : isOT (succ (ρ.v r)) = true := isOT_succ hVot
  have hVlt : ρ.v r < succ (ρ.v r) := lt_succ_self _
  have hBot : isOT (t2B (ρ.v r) ρ Lc) = true := by
    have := I.fo r hrM Lc (r + L) [] hCL
    exact isOT_arg this
  have hσB : sh (ρ.v r) (succ (ρ.v r)) (t2B (ρ.v r) ρ Lc) = t2B (ρ.v r) ρ Lc :=
    tame_sigmaB_std hM hS I hlen hr hq hXu hCL
  unfold t2W1
  rw [hCLT]
  rcases List.eq_nil_or_concat Lc with hnil | ⟨L', c, hLc⟩
  · subst hnil
    show ¬ _ < sh (τ.v r) (succ (ρ.v r)) z
    rw [sh_z]
    exact T.not_lt_z _
  rw [List.concat_eq_append] at hLc
  subst hLc
  have hcT : c ∈ CL (M.take (r + L)) r := by rw [hCLT]; simp
  have hcCL : c ∈ CL M r := by rw [hCL]; simp
  have hcx : c < r + L := by
    have := (mem_children (cl_mem_children hcT)).2; rw [List.length_take] at this; omega
  have hcTL : c < (M.take (r + L)).length := by rw [List.length_take]; omega
  obtain ⟨hvτ, hmap, _⟩ := frame_take (show (r + L) + 1 = M.length from hlen) I.r0p I.z2 I.sd I.z1 I.uat I.uab
    I.cons I.good hτ hRk1 hrx (L := L') (c := c) (R := []) hCLT
  -- the forms of the children
  obtain ⟨hsT, hpT⟩ := cl_vals hτ hG hrT
  obtain ⟨hsM, hpM⟩ := cl_vals I.cons I.good hrM
  rw [hCLT] at hsT hpT
  rw [hCL] at hsM hpM
  simp only [List.map_append, List.map_singleton] at hsT hpT hsM hpM
  obtain ⟨s', y', hsy'⟩ := (hsT (τ.o c) (by simp)).2
  obtain ⟨s, y, hsy⟩ := (hsM (ρ.o c) (by simp)).2
  have hsT' : ∀ t ∈ L'.map τ.o ++ [psi s' y' z], Single t := by rw [← hsy']; exact hsT
  have hpT' : (L'.map τ.o ++ [psi s' y' z]).Pairwise (fun a b => b ≤ a) := by rw [← hsy']; exact hpT
  have hpM1 := (List.pairwise_append.mp hpM).1
  have hsM' : ∀ t ∈ L'.map ρ.o ++ [psi s y z], Single t := by
    intro t ht
    apply hsM t
    rw [← hsy] at ht
    exact List.mem_append_left _ ht
  have hpM' : (L'.map ρ.o ++ [psi s y z]).Pairwise (fun a b => b ≤ a) := by rw [← hsy]; exact hpM1
  have hXe : spArg (ρ.v r) z (sumN ((L' ++ [c]).map τ.o)) =
      step (ρ.v r) (spArg (ρ.v r) z (sumN (L'.map ρ.o))) s' y' z := by
    rw [List.map_append, List.map_singleton, hsy', spArg_snoc hsT' hpT', hmap]
  have hBe : t2B (ρ.v r) ρ (L' ++ [c]) = step (ρ.v r) (spArg (ρ.v r) z (sumN (L'.map ρ.o))) s y z := by
    unfold t2B
    rw [List.map_append, List.map_singleton, hsy, spArg_snoc hsM' hpM']
  set B' := spArg (ρ.v r) z (sumN (L'.map ρ.o)) with hB'def
  have hocT : isOT (psi s' y' z) = true := (hsT' _ (by simp)).1
  have hocM : isOT (psi s y z) = true := (hsM' _ (by simp)).1
  -- `o_T(c) ≤ o_M(c)`
  have hagc := agree_of_cons hτ hC1 hRk1 c hcTL
  have hle : psi s' y' z ≤ psi s y z := by
    have hD := (Ctx.drop (by omega)).1
    rw [hx1] at hD
    have hPO := (hD c hcx).1.1
    have h' : (drop1 M (r + L) rk).o c ≤ ρ.o c := by
      rcases hPO with h | ⟨h, _⟩
      · exact LhdE.le h
      · exact DRelOA.le (Or.inr h)
    rw [← hagc.1, hsy', hsy] at h'
    exact h'
  -- `X ≤ B`
  have hXB : step (ρ.v r) B' s' y' z ≤ step (ρ.v r) B' s y z := by
    by_cases htT : lt B' y' = true ∧ lt (psi (ρ.v r) z z) (psi s' y' z) = true
    · have hy' : y' ≠ z := by
        intro h0; rw [h0] at htT; exact T.not_lt_z _ htT.1
      obtain ⟨yM, hyM, hyy⟩ := t2SVc0'_of_dropV3 I Ctx hlen hr τ hτ L' c hCLT s' y' hsy' hy'
      rw [hsy] at hyM
      simp only [psi.injEq] at hyM
      obtain ⟨rfl, rfl, -⟩ := hyM
      rcases (le_iff _ _).mp hyy with hlt | heq
      · have htM := trig_mono hlt htT.1 htT.2
        unfold step
        rw [if_pos htT, if_pos htM]
        exact H_mono hocT hocM hyy
      · rw [heq]
    · have htM : ¬ (lt B' y = true ∧ lt (psi (ρ.v r) z z) (psi s y z) = true) := fun h =>
        htT (hNS τ hτ L' c s y s' y' rfl hsy hsy' h)
      unfold step
      rw [if_neg htT, if_neg htM]
      exact add_le_add_left _ hle
  have hXot : isOT (spArg (ρ.v r) z (sumN ((L' ++ [c]).map τ.o))) = true := by
    have := hG.ot_o r hrT
    rw [o_cl_eq hτ hG hrT, hCLT, hvτ] at this
    exact isOT_arg this
  have hle1 : spArg (ρ.v r) z (sumN ((L' ++ [c]).map τ.o)) ≤ t2B (ρ.v r) ρ (L' ++ [c]) := by
    rw [hBe, hXe]; exact hXB
  have hle2 : sh (ρ.v r) (succ (ρ.v r)) (spArg (ρ.v r) z (sumN ((L' ++ [c]).map τ.o))) ≤
      t2B (ρ.v r) ρ (L' ++ [c]) := by
    have := sh_le_sh hVot hVs (le_of_lt hVlt) hXot hBot hle1
    rwa [hσB] at this
  rw [hvτ]
  exact fun h => lt_irrefl' _ (lt_of_lt_of_le h hle2)

#print axioms qr_w1_of

/-- `SeedPFResV3R4` with `QRNoSwitch` in place of `QRRelR`. -/
structure SeedPFResV3R6 (M : Mat) (ρ : Valn) : Prop where
  qr : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    (∀ i, upg M i ≠ some (r + L)) → ∀ Lc, CL M r = Lc ++ [r + L] → QRNoSwitch M ρ r L Lc
  sv : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    upg M (r + L - 1) = some (r + L) → SVRel M ρ r L
  C1 : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = none → CRelR M ρ r L q
  C2r : ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFr QPF M r L r

theorem seedPFResV3R4_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (Ctx : StepCtx3 M ρ rk) (h : SeedPFResV3R6 M ρ) : SeedPFResV3R4 M ρ :=
  ⟨fun r L hlen hr hq hXu Lc hLc => ⟨qr_w1_of hM hS I Ctx hlen hr hq hXu hLc (h.qr r L hlen hr hq hXu Lc hLc)⟩,
    h.sv, h.C1, h.C2r⟩

/-- `SeedVFResV3R5` with `SeedPFResV3R6`. -/
structure SeedVFResV3R6 (M : Mat) (ρ : Valn) : Prop where
  pf : SeedPFResV3R6 M ρ
  qnDom : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → T2SeedQNDom M ρ r L q Lc
  cDom : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = none → T2SeedCDomR M ρ r L q
  C2r : ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFr QVF M r L r

theorem seedVFResV3R5_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (Ctx : StepCtx3 M ρ rk) (h : SeedVFResV3R6 M ρ) : SeedVFResV3R5 M ρ :=
  ⟨seedPFResV3R4_of hM hS I Ctx h.pf, h.qnDom, h.cDom, h.C2r⟩

section
variable (hDI : HDropInputsV3) (hF : HFrameV3)
    (hAbsU : T0AtV3 (fun M ρ r L => T0AbsWU M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ))
    (hQR : HQRInputsStepV3) (hQN : HQNInputsV3)
    (hBXU2 : T2AtV3 (fun M ρ => T2BelowAtV3U2 M ρ))
    (hCanH2 : HCanonHard2)
    (hVF6 : T2AtV3 (fun M ρ => SeedVFResV3R6 M ρ))
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

include hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2 hVF6 hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG

/-- **Order preservation of the translation below SRO** from the current residuals (`SeedVFResV3R6`). -/
theorem translation_order_res11
    {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA :=
  translation_order_res10 hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2
    (fun M ρ rk C hz h2 => seedVFResV3R5_of C.std C.ne (coreW C.S C.I) C (hVF6 M ρ rk C hz h2))
    hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG hA hB hAS hBE hlt

/-- **Surjectivity of the translation below SRO** from the current residuals and `EvalFSNZ 2`. -/
theorem translation_surj_res11 (hFS : EvalFSNZ 2)
    {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  translation_surj_res10 hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2
    (fun M ρ rk C hz h2 => seedVFResV3R5_of C.std C.ne (coreW C.S C.I) C (hVF6 M ρ rk C hz h2))
    hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG hFS hot hvN hlt

end

#print axioms translation_order_res11
#print axioms translation_surj_res11

end Ytosk.V3Main.SeedPF
