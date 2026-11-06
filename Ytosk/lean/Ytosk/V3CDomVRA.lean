/-
**t = 2, C1: `T2SeedCDomR` from `T2VRASeedC` (2026-11-07).**

The same idea as `t2SeedQNDom_ofF` (V3QNDomF).  At `n = 2`, the last frame of `r` in `N = M[2]` is `q` with
`o_N(q) = ψ_{s'}(σ X₁)` (`seed_last_CV3`), the state before it is `X₁`.  `X₁ < σ X₁` (the field `strict`, so `X₁ ≠ 0`) is
the trigger, the summands of `σ X₁` are high (`c_hi_of_decP`), and `QVRAt` at the level `u = V` says: the components of `s'`
at the level `V` are below `Ω_{s'}` or `X₁` (`comps V V = []`).  So `cDom` is no longer a residual.
-/
import Ytosk.V3QNDomF

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

theorem t2SeedCDomR_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowAtV3U M ρ)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q])
    (hun : upg M (r + L - 1) = none) (hCR2 : CRelR2 M ρ r L q) (hBig : T2SeedCBig M ρ r L q)
    (hC : T2VRASeedC M) : T2SeedCDomR M ρ r L q := by
  intro τ hτ g hg
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hL0 : 0 < L := by omega
  have hrM : r < M.length := by omega
  have hlen2 : 2 ≤ M.length := by omega
  have hx1 : M.length - 1 = r + L := by omega
  have hVot : isOT (ρ.v r) = true := I.good.ot_v r hrM
  have hhi := c_hi_of_decP I Ctx hlen hL0 hCR2.decP
  have hCR : CRel M ρ r L q := cRel_of hM hS I hlen hr hq hqr hun
    ⟨hCR2.decP, c_rw_ofV3 I Ctx hlen hL0 hCR2.strict hhi⟩
  have hFix := t2SeedCFix_ofV3 hM hS I Ctx hlen hr hq hqr hncl hCR hBig
  -- `N = M[2]` and its valuation
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = G2 M r L m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, hx1]; exact hr)
    rw [h2, hx1] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hGall := good3_expand_t2V3 hM hS I (Ctx.drop (len2_of_t2 Ctx hz h2)) hz h2
    (t2BelowXE_V3U hB hM hS I (Ctx.drop (len2_of_t2 Ctx hz h2)) hz h2) (t2CopyResV3 hM hS I hz h2)
  have hGlow : ∀ m, 1 ≤ m → m < 2 → ∀ τ', Cons (G2 M r L m) τ' → Good3 (G2 M r L m) τ' :=
    fun m hm _ τ' hτ' => by rw [← hexp m] at hτ' ⊢; exact hGall m hm τ' hτ'
  have hGlow2 : ∀ τ', Cons (G2 M r L 2) τ' → Good3 (G2 M r L 2) τ' :=
    fun τ' hτ' => by rw [← hexp 2] at hτ' ⊢; exact hGall 2 (by omega) τ' hτ'
  obtain ⟨rkN, hRN⟩ := rk_expand_t2 hX hJ hz h2 I.rank 2 (by omega)
  rw [hexp 2] at hRN
  have hCN : Cons (G2 M r L 2) (rhsIt (G2 M r L 2) (rkBound (G2 M r L 2) rkN)) := cons_of_rk hRN
  have hGN : Good3 (G2 M r L 2) (rhsIt (G2 M r L 2) (rkBound (G2 M r L 2) rkN)) :=
    hGlow2 _ hCN
  generalize rhsIt (G2 M r L 2) (rkBound (G2 M r L 2) rkN) = σ at hCN hGN
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [hx1] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  obtain ⟨_, _, hCLN, hval, hvr, _, _, hoq, _, hX1n⟩ :=
    seed_last_CV3 hM hS I Ctx hz h2 hlen hr hq hqr hncl hCR hFix hτ hRk1 2 (le_refl 2) hGlow σ hCN hGN
  have hv0 : τ.v r = ρ.v r := v_take_of_untopped I hlen hrx (topP_C hM hS I hlen hr hq hqr) hτ
  -- `X₁ ≠ 0`
  have hst := hCR2.strict τ hτ
  have hX0 : t2X1 M r L τ ≠ z := by
    intro h0
    rw [h0, sh_z] at hst
    exact lt_irrefl' _ hst
  obtain ⟨hin, _⟩ := hX1n hX0
  have hoq' : σ.o q = psi (qnS M ρ r L q) (sh (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ)) z := by
    rw [hoq, hin]; rfl
  have hstate : spArg (σ.v r) z (sumN ((CL (M.take (r + L)) r).map σ.o)) = t2X1 M r L τ := by
    rw [List.map_congr_left hval, hvr]
    unfold t2X1
    rw [hv0]
  have hQ := hC r L hlen hr ⟨q, hq, hqr, hncl⟩ 2 (le_refl 2) σ hCN hGN (CL (M.take (r + L)) r) q [] hCLN
    (ρ.v r) (Or.inl hvr.symm)
  have hsp := (split_all_hi (hhi τ hτ)).1
  have hne : sh (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) ≠ z := sh_ne_z hX0
  have hres := hQ _ _ hoq'
    (by
      rw [hstate, hvr]
      exact ⟨hst, psi_lt_psi_z_iff.mpr (Or.inl (qnS_gt M ρ r L q))⟩)
    (by rw [hsp]; exact hne)
    (by rw [hvr]; exact fun h => lt_irrefl' _ h)
    g hg
  rw [hstate, hvr] at hres
  rcases hres with h | h | ⟨d, hd, _⟩
  · exact Or.inl h
  · exact Or.inr h
  · rw [comps_self_nil hVot] at hd; simp at hd

#print axioms t2SeedCDomR_of

/-- `SeedVFResV3R8` without `cDom`. -/
structure SeedVFResV3R9 (M : Mat) (ρ : Valn) : Prop where
  pf : SeedPFResV3R7 M ρ
  qnDomF : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → T2SeedQNDomF M ρ r L q Lc
  C2r : ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFr QVF M r L r

theorem seedVFResV3R8_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowAtV3U M ρ)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hCan : HCanon) (hC : T2VRASeedC M) (h : SeedVFResV3R9 M ρ) : SeedVFResV3R8 M ρ := by
  refine ⟨h.pf, h.qnDomF, fun r L q hlen hr hq hqr hncl hun => ?_, h.C2r⟩
  have hC1 := h.pf.C1 r L q hlen hr hq hqr hncl hun
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  rw [show M.length - 1 = r + L by omega] at hRk1
  have hTS : M.take (r + L) ≠ SRO := ne_SRO_of_rk hRk1
  have hTstd : Std (M.take (r + L)) := std_take hM (r + L) (by omega)
  have hBig : T2SeedCBig M ρ r L q := t2SeedCBig_of_canonicalV3 hM hS I Ctx hlen hr hq hqr hncl hun hC1.decP
    (fun τ hτ hG => hCan _ τ rk hTstd hTS hτ hRk1 hG)
  exact t2SeedCDomR_of hB hM hS I Ctx hz h2 hlen hr hq hqr hncl hun hC1 hBig hC

section
variable (hDI : HDropInputsV3) (hF : HFrameV3)
    (hAbsU : T0AtV3 (fun M ρ r L => T0AbsWU M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ))
    (hQR : HQRInputsStepV3) (hQN : HQNInputsV3)
    (hBXU2 : T2AtV3 (fun M ρ => T2BelowAtV3U2 M ρ))
    (hCanH2 : HCanonHard2)
    (hVF9 : T2AtV3 (fun M ρ => SeedVFResV3R9 M ρ))
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

include hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2 hVF9 hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG

/-- **Order preservation of the translation below SRO** from the current residuals (`SeedVFResV3R9`). -/
theorem translation_order_res14
    {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA :=
  translation_order_res13 hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2
    (fun M ρ rk C hz h2 => seedVFResV3R8_of (t2BelowAtV3U_of C hz h2 (hBXU2 M ρ rk C hz h2)) C.std C.ne
      (coreW C.S C.I) C hz h2 (hCanon_of_hard (hCanonHard_of_2 hCanH2)) (hSC M ρ rk C hz h2) (hVF9 M ρ rk C hz h2))
    hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG hA hB hAS hBE hlt

/-- **Surjectivity of the translation below SRO** from the current residuals and `EvalFSNZ 2`. -/
theorem translation_surj_res14 (hFS : EvalFSNZ 2)
    {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  translation_surj_res13 hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2
    (fun M ρ rk C hz h2 => seedVFResV3R8_of (t2BelowAtV3U_of C hz h2 (hBXU2 M ρ rk C hz h2)) C.std C.ne
      (coreW C.S C.I) C hz h2 (hCanon_of_hard (hCanonHard_of_2 hCanH2)) (hSC M ρ rk C hz h2) (hVF9 M ρ rk C hz h2))
    hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG hFS hot hvN hlt

end

#print axioms translation_order_res14
#print axioms translation_surj_res14

end Ytosk.V3Main.SeedPF
