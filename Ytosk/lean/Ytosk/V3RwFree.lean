/-
**t = 2: the fields `rw` of the sv and C seeds without `k` (2026-11-07).**

`SVRel.rw` (for every `k`, the frame of `r` keeps `σ^{k+1} X₁`) follows from `X₁ < σ X₁` (`T2SVStrict`, `sv_rw_of`).
`CRelR.rw` follows from `X₁ < σ X₁` and the lower bound `Ω_{s'+1}` of the summands of `σ X₁` (`c_rw_of_base` reads only
these and the standard form of `X₁`, which is the argument of `o(r)` in `M.take x`).
-/
import Ytosk.V3QRW1

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

theorem sv_rw_ofV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    (hSt : T2SVStrict M ρ r L) :
    ∀ τ, Cons (M.take (r + L)) τ → ∀ k,
      step (ρ.v r) (t2X1 M r L τ) (succ (ρ.v r))
        (sh (ρ.v r) (succ (ρ.v r)) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k)) z =
      sh (ρ.v r) (succ (ρ.v r)) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k) := by
  intro τ hτ k
  obtain ⟨hG, hvr, hch⟩ := sv_children_ctxV3 hM hS I Ctx hlen hr hq hux hτ
  have hrT : r < (M.take (r + L)).length := by
    have := par_lt M 0 _ _ hq; rw [List.length_take]; omega
  have hV : isOT (ρ.v r) = true := I.good.ot_v r (by omega)
  have hV' : isOT (succ (ρ.v r)) = true := isOT_succ hV
  have hVV : ρ.v r < succ (ρ.v r) := lt_succ_self _
  have hVw : ρ.v r < succ (succ (ρ.v r)) := lt_trans hVV (lt_succ_self _)
  -- `X₁` is standard and its summands are at least `Ω_{V+2}`
  have hX1 : isOT (t2X1 M r L τ) = true := by
    have := hG.ot_o r hrT
    rw [o_cl_eq hτ hG hrT] at this
    exact isOT_arg this
  have hq1 : ∀ q ∈ summands (t2X1 M r L τ), ¬ q < Om (succ (succ (ρ.v r))) := by
    unfold t2X1
    have hsing : ∀ t ∈ (CL (M.take (r + L)) r).map τ.o, Single t := by
      intro t ht
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
      exact single_o hτ hG (mem_children (cl_mem_children hd)).2
    apply summands_spArg_ge _ z (isOT_sumN _ (fun t ht => (hsing t ht).1)) (by simp [summands])
    intro q hq hlt
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (summands_sumN_sub hsing q hq)
    have hdc := cl_mem_children hd
    have hdT := (mem_children hdc).2
    have hlt' := hch d hdc
    obtain ⟨y, hy⟩ := o_psi_sub hτ hdT
    rw [sf_ot (hG.ot_v d hdT)] at hy
    rw [hy, Om] at hlt
    rcases psi_lt_psi_z_iff.mp hlt with h | ⟨_, h⟩
    · exact lt_irrefl' _ (lt_of_lt_of_le h (succ_le_of_lt hlt'))
    · exact not_lt_z _ h
  obtain ⟨hk1, hk2, hk3⟩ := shIt_facts hV hV' hVV hVw hX1 hq1 (k + 1)
  have hY : shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) (k + 1) =
      sh (ρ.v r) (succ (ρ.v r)) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k) := rfl
  rw [hY] at hk1 hk2 hk3
  have hlt : t2X1 M r L τ < sh (ρ.v r) (succ (ρ.v r)) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k) := by
    obtain ⟨_, hk2', _⟩ := shIt_facts hV hV' hVV hVw hX1 hq1 k
    exact lt_of_lt_of_le (hSt τ hτ) (sh_le_sh hV hV' (le_of_lt hVV) hX1 (shIt_facts hV hV' hVV hVw hX1 hq1 k).1 hk2')
  unfold step
  rw [if_pos ⟨hlt, psi_lt_psi_z_iff.mpr (Or.inl hVV)⟩]
  exact H_of_high hV' (fun q hq h => hk3 q hq h)

/-- `CRelR.rw` from `X₁ < σ X₁` and the summands of `σ X₁`. -/
theorem c_rw_ofV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hrL : 0 < L)
    (hst : ∀ τ, Cons (M.take (r + L)) τ → t2X1 M r L τ < sh (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ))
    (hhiA : ∀ τ, Cons (M.take (r + L)) τ → ∀ g ∈ summands (sh (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ)),
      ¬ g < psi (succ (qnS M ρ r L q)) z z) :
    ∀ τ, Cons (M.take (r + L)) τ → ∀ k,
      step (ρ.v r) (t2X1 M r L τ) (qnS M ρ r L q) (step (qnS M ρ r L q) z (qnS M ρ r L q)
        (sh (ρ.v r) (qnS M ρ r L q) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) k)) z) z =
      sh (ρ.v r) (qnS M ρ r L q) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) k) := by
  intro τ hτ k
  have hrM : r < M.length := by omega
  have hV : isOT (ρ.v r) = true := I.good.ot_v r hrM
  have hs : isOT (qnS M ρ r L q) = true := qnS_ot I hrM L q
  have hVV := qnS_gt M ρ r L q
  have hlt0 := hst τ hτ
  have hhi := hhiA τ hτ
  have hx1 : M.length - 1 = r + L := by omega
  have hτ' : Cons (M.take (M.length - 1)) τ := by rw [hx1]; exact hτ
  have hG := good3_take_anyV3U I (Ctx.drop (by omega)) (by omega) hτ'
  rw [hx1] at hG
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hot : isOT (t2X1 M r L τ) = true := by
    have := hG.ot_o r hrT
    rw [o_cl_eq hτ hG hrT] at this
    exact isOT_arg this
  set V := ρ.v r
  set s' := qnS M ρ r L q
  set X1 := t2X1 M r L τ
  have hX1z : X1 ≠ z := by
    intro h0
    rw [h0, sh_z] at hlt0
    exact lt_irrefl' _ hlt0
  have hY : sh V s' (shIt V s' X1 k) = shIt V s' (sh V s' X1) k := shIt_succ' X1 k
  have hhigh : ∀ g ∈ summands (sh V s' (shIt V s' X1 k)), ¬ g < psi (succ s') z z := by
    rw [hY]; exact b0_shIt hV hs hVV (isOT_sh hV hs hVV hot) hhi k
  have hne : sh V s' (shIt V s' X1 k) ≠ z := sh_ne_z (shIt_ne_z hX1z k)
  have hzlt : z < sh V s' (shIt V s' X1 k) := z_lt_of_ne_z hne
  have hin : step s' z s' (sh V s' (shIt V s' X1 k)) z = sh V s' (shIt V s' X1 k) := by
    unfold step
    rw [if_pos ⟨hzlt, psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hzlt⟩)⟩]
    exact H_of_high hs hhigh
  have hchain : ∀ j, sh V s' X1 ≤ sh V s' (shIt V s' X1 j) := by
    intro j
    induction j with
    | zero => exact le_refl _
    | succ j ih =>
      exact le_trans ih (le_sh hV hs (le_of_lt hVV) (isOT_sh hV hs hVV (isOT_shIt_svc hV hs hVV hot j)))
  rw [hin]
  unfold step
  rw [if_pos ⟨lt_of_lt_of_le hlt0 (hchain k), psi_lt_psi_z_iff.mpr (Or.inl hVV)⟩]
  exact H_of_high hs hhigh

/-- `CRelR` with the `k`-free fields. -/
structure CRelR2 (M : Mat) (ρ : Valn) (r L q : Nat) : Prop where
  decP : ∀ τ, Cons (M.take (r + L)) τ → ∀ Lc c0, CL (M.take (r + L)) r = Lc ++ [c0] →
    ∃ s y, τ.o c0 = psi s y z ∧ qnS M ρ r L q < s
  strict : ∀ τ, Cons (M.take (r + L)) τ → t2X1 M r L τ < sh (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ)
  hi : ∀ τ, Cons (M.take (r + L)) τ → ∀ g ∈ summands (sh (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ)),
    ¬ g < psi (succ (qnS M ρ r L q)) z z

/-- `SeedPFResV3R6` with the `k`-free fields. -/
structure SeedPFResV3R7 (M : Mat) (ρ : Valn) : Prop where
  qr : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    (∀ i, upg M i ≠ some (r + L)) → ∀ Lc, CL M r = Lc ++ [r + L] → QRNoSwitch M ρ r L Lc
  sv : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    upg M (r + L - 1) = some (r + L) → T2SVStrict M ρ r L
  C1 : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = none → CRelR2 M ρ r L q
  C2r : ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFr QPF M r L r

theorem seedPFResV3R6_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (Ctx : StepCtx3 M ρ rk) (h : SeedPFResV3R7 M ρ) : SeedPFResV3R6 M ρ :=
  ⟨h.qr, fun r L hlen hr hq hux => ⟨sv_rw_ofV3 hM hS I Ctx hlen hr hq hux (h.sv r L hlen hr hq hux)⟩,
    fun r L q hlen hr hq hqr hncl hun => ⟨(h.C1 r L q hlen hr hq hqr hncl hun).decP,
      c_rw_ofV3 I Ctx hlen (by have := par_lt M 2 _ _ hr; omega) (h.C1 r L q hlen hr hq hqr hncl hun).strict
        (h.C1 r L q hlen hr hq hqr hncl hun).hi⟩, h.C2r⟩

/-- `SeedVFResV3R6` with `SeedPFResV3R7`. -/
structure SeedVFResV3R7 (M : Mat) (ρ : Valn) : Prop where
  pf : SeedPFResV3R7 M ρ
  qnDom : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → T2SeedQNDom M ρ r L q Lc
  cDom : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = none → T2SeedCDomR M ρ r L q
  C2r : ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFr QVF M r L r

theorem seedVFResV3R6_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (Ctx : StepCtx3 M ρ rk) (h : SeedVFResV3R7 M ρ) : SeedVFResV3R6 M ρ :=
  ⟨seedPFResV3R6_of hM hS I Ctx h.pf, h.qnDom, h.cDom, h.C2r⟩

section
variable (hDI : HDropInputsV3) (hF : HFrameV3)
    (hAbsU : T0AtV3 (fun M ρ r L => T0AbsWU M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ))
    (hQR : HQRInputsStepV3) (hQN : HQNInputsV3)
    (hBXU2 : T2AtV3 (fun M ρ => T2BelowAtV3U2 M ρ))
    (hCanH2 : HCanonHard2)
    (hVF7 : T2AtV3 (fun M ρ => SeedVFResV3R7 M ρ))
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

include hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2 hVF7 hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG

/-- **Order preservation of the translation below SRO** from the current residuals (`SeedVFResV3R7`). -/
theorem translation_order_res12
    {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA :=
  translation_order_res11 hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2
    (fun M ρ rk C hz h2 => seedVFResV3R6_of C.std C.ne (coreW C.S C.I) C (hVF7 M ρ rk C hz h2))
    hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG hA hB hAS hBE hlt

/-- **Surjectivity of the translation below SRO** from the current residuals and `EvalFSNZ 2`. -/
theorem translation_surj_res12 (hFS : EvalFSNZ 2)
    {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  translation_surj_res11 hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2
    (fun M ρ rk C hz h2 => seedVFResV3R6_of C.std C.ne (coreW C.S C.I) C (hVF7 M ρ rk C hz h2))
    hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG hFS hot hvN hlt

end

#print axioms sv_rw_ofV3
#print axioms c_rw_ofV3
#print axioms translation_order_res12
#print axioms translation_surj_res12

end Ytosk.V3Main.SeedPF
