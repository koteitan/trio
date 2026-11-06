/-
**t = 2, qn: the field `QNRelR3.base` is proved (2026-11-06).**

`qn_take_t1L` (V3QNTakeL) on the V3 context: the state of `r` in `M.take x` is `B + Ω_{t₁}` with `t₁ = V + ω_T`, `ω_T` a
single term, so `V < t₁`.  The bundles `SeedPFResV3R4`, `SeedVFResV3R4` drop the field `qn` altogether.
-/
import Ytosk.V3C2Shape2
import Ytosk.V3QNTakeL

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Classical in
theorem qn_take_t1LV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) {Lc : List Nat} (hCLM : CL M r = Lc ++ [q])
    {τ : Valn} (hτ : Cons (M.take (r + L)) τ) :
    ∃ ωT, spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) =
        app (t2B (ρ.v r) ρ Lc) (psi (add (ρ.v r) ωT) z z) ∧ τ.v q = add (ρ.v r) ωT ∧
      isOT ωT = true ∧ (∃ a b, ωT = psi a b z) ∧
      ωT ≤ omega (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q))) ∧
      ρ.v q = add (ρ.v r)
        (omega (succ (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q))))) := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hqcl : q ∈ CL M r := by rw [hCLM]; simp
  have hpq : par M 0 q = some r := (mem_children_iff.mp (cl_mem_children hqcl)).2
  have hrq : r < q := par_lt M 0 _ _ hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hL0 : 0 < L := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, Tqb, _, TCLq, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Txb Tqb TCLq
  have hqb : ∀ a, par M 0 q = some a → col M q ≠ bump M a := by
    intro a ha; rw [hpq] at ha; cases ha; exact Tqb
  have hr1 : par M 1 (r + L) = some r := par1_x_r (by omega) hX.z2 hX.loc.2.1 hr
  have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
  have he1q : entry M 1 (r + L) = entry M 1 q :=
    e1_of_col (show col M (r + L) = (entry M 0 q + 1, entry M 1 q, 1) from Txb)
  have he2q : entry M 2 q = 1 := I.be q (r + L) hxq Txb
  have he0lt := anc0_e0_lt hA (by omega)
  have hpar1q : par M 1 q = some r :=
    par1_q (n := 2) (d0 := entry M 0 (r + L) - entry M 0 r) (d1 := entry M 1 (r + L) - entry M 1 r)
      hlen hL0 hA hq (by omega) (le_refl 2) (by omega) he2r h1lt hqb hr1 hqr Txb
  -- the drop
  have hx1 : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have hdrop := (Ctx.drop (by omega)).1
  have J1 := Ctx.pre (M.length - 1) (by omega) (by omega)
  have hG1 := good3_congr J1.good (agree_of_cons J1.cons hC1 J1.rank)
  have hpre : ∀ i, i < M.length - 1 → ∃ Tl, CL M i = CL (M.take (M.length - 1)) i ++ Tl :=
    fun i hi => cl_prefix hx1 I.r0p I.z2 I.sd I.z1 I.uat hi
  have hfr := fun i (hi : i < M.length - 1) (h : CL (M.take (M.length - 1)) i = Lc ++ q :: []) =>
    frame_take hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 hi h
  rw [show M.length - 1 = r + L by omega] at hRk1 hC1 hdrop hG1 hpre hfr
  set ρ' := rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rk) with hρ'
  have hTlen : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hag := agree_of_cons hτ hC1 hRk1
  -- `CL_T(q) = []`
  obtain ⟨Tl, hTl⟩ := hpre q hqx
  rw [TCLq] at hTl
  have hCLTq : CL (M.take (r + L)) q = [] := (List.append_eq_nil_iff.mp hTl.symm).1
  -- `q` is counted in `M.take x` too: it is topped in `M`, so not upgraded
  have hcqM : children M q = (children M q).filter (fun d => decide (d < r + L)) ++ [r + L] :=
    split_last_max _ _ (children_sorted M _) hxq (fun d hd => by have := (mem_children hd).2; omega)
  have htopM : topped M q = true := by
    unfold topped; rw [hcqM, List.getLast?_append]; simp [Txb]
  have hcntM : Counted M r q := by
    unfold CL at hqcl; simpa using (List.mem_filter.mp hqcl).2
  have hupM : isUpg M q = false := by
    cases h : isUpg M q
    · rfl
    · exact absurd ⟨h, htopM⟩ hcntM.2
  have hux : upg M (r + L - 1) ≠ some q := by
    intro hu
    have h' : isUpg M q = true := by
      unfold isUpg; rw [List.any_eq_true]
      exact ⟨r + L - 1, List.mem_range.mpr (by omega), by simp [hu]⟩
    rw [hupM] at h'; cases h'
  have hupT : isUpg (M.take (r + L)) q = false := by
    rw [isUpg_take_eq hlen hux hqx]; exact hupM
  have hcntT : Counted (M.take (r + L)) r q := by
    refine ⟨?_, fun h => by rw [hupT] at h; cases h.1⟩
    rw [col_take M hqx, bump_take M (show r < r + L by omega)]; exact hcntM.1
  have hqclT : q ∈ CL (M.take (r + L)) r := by
    unfold CL
    refine List.mem_filter.mpr ⟨?_, by simpa using hcntT⟩
    rw [children_take]; exact List.mem_filter.mpr ⟨cl_mem_children hqcl, by simpa using hqx⟩
  -- `CL_T(r) = Lc ++ [q]`
  obtain ⟨Tl', hTl'⟩ := hpre r (by omega)
  rw [hCLM] at hTl'
  have hnd : (Lc ++ [q]).Nodup := by
    rw [← hCLM]; unfold CL children; exact (List.nodup_range.filter _).filter _
  have hCLTr : CL (M.take (r + L)) r = Lc ++ [q] := by
    rcases List.eq_nil_or_concat Tl' with h | ⟨T0, a, h⟩
    · rw [h, List.append_nil] at hTl'; exact hTl'.symm
    · exfalso
      rw [h, List.concat_eq_append, ← List.append_assoc] at hTl'
      obtain ⟨hLc, -⟩ := List.append_inj' hTl' rfl
      have hqLc : q ∈ Lc := by rw [hLc]; exact List.mem_append_left _ hqclT
      rw [List.nodup_append] at hnd
      exact absurd rfl (hnd.2.2 q hqLc q (by simp))
  obtain ⟨hvr, hLo, -⟩ := hfr r (by omega) hCLTr
  have hqT : q < (M.take (r + L)).length := by omega
  have hoq : ρ'.o q = psi (ρ'.v q) z z := by
    rw [o_cl_eq hC1 hG1 hqT, hCLTq]; rfl
  set Lq := (children M q).filter (fun d => decide (d < r + L)) with hLq
  have hbT : ∀ j ∈ Lq, bumpTerm (M.take (r + L)) ρ' q j ≤ bumpTerm M ρ q j := by
    intro j hjL
    have hjq : j ∈ children M q := (List.mem_filter.mp hjL).1
    have hjx : j < r + L := by simpa using (List.mem_filter.mp hjL).2
    have hpj : par M 0 j = some q := (mem_children_iff.mp hjq).2
    unfold bumpTerm
    rw [col_take M hjx, bump_take M hqx]
    split
    · have hch : children (M.take (r + L)) j = children M j := by
        rw [children_take, List.filter_eq_self]
        intro c hc
        simpa using kid_lt_x hpj hq hjx (mem_children_iff.mp hc).2
      rw [hch]
      have hcx : ∀ c ∈ children M j, c < r + L := fun c hc => kid_lt_x hpj hq hjx (mem_children_iff.mp hc).2
      apply omega_le_omega
      · exact isOT_sumN _ (fun t ht => by
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht; exact hG1.ot_o c (by have := hcx c hc; omega))
      · exact isOT_sumN _ (fun t ht => by
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht; exact I.good.ot_o c (mem_children hc).2)
      · apply sumN_le2 (forall₂_map_le _ (fun c hc => po_le (hdrop c (hcx c hc)).1))
        · intro t ht; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht; exact hG1.ot_o c (by have := hcx c hc; omega)
        · intro t ht; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht; exact I.good.ot_o c (mem_children hc).2
    · exact le_refl _
  have hOT1 : ∀ t ∈ one :: Lq.map (bumpTerm (M.take (r + L)) ρ' q), isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG1 q j
  have hOT2 : ∀ t ∈ one :: Lq.map (bumpTerm M ρ q), isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm I.good q j
  have hvq : ρ'.v q = add (ρ.v r) (omega (sumN (one :: Lq.map (bumpTerm (M.take (r + L)) ρ' q)))) := by
    rw [(hC1 q hqT).2]; unfold vRhs
    rw [entry_take M 1 hqx, entry_take M 2 hqx, if_neg (by omega), if_neg (by omega), par_take M 1 q hqx,
      hpar1q, children_take]
    show sf (add (ρ'.v r) _) = _
    rw [hvr, sf_ot (isOT_add (I.good.ot_v r (by omega)) (isOT_omega (isOT_sumN _ hOT1)))]
  -- `v_M(q) = V + ω^{S+1}`: the bump term of `x` is `1`
  have hSot : isOT (sumN (one :: Lq.map (bumpTerm M ρ q))) = true := isOT_sumN _ hOT2
  have hbx : bumpTerm M ρ q (r + L) = one := by
    unfold bumpTerm; rw [if_pos Txb]
    have hnil : children M (r + L) = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro c hc
      have h1 := (mem_children hc).2
      have h2 := par_lt M 0 c (r + L) (mem_children_iff.mp hc).2
      omega
    rw [hnil]; rfl
  have hvqM : ρ.v q = add (ρ.v r) (omega (succ (sumN (one :: Lq.map (bumpTerm M ρ q))))) := by
    rw [(I.cons q (by omega)).2]; unfold vRhs
    rw [if_neg (by omega), if_neg (by omega), hpar1q, hcqM, List.map_append, List.map_singleton, hbx,
      ← List.cons_append, sumN_snoc, add_one_eq_succ hSot, sf_ot (isOT_succ hSot)]
    show sf (add (ρ.v r) _) = _
    rw [sf_ot (isOT_add (I.good.ot_v r (by omega)) (isOT_omega (isOT_succ hSot)))]
  -- the argument of `r` in `M.take x`
  have hvalsT := cl_vals hC1 hG1 (show r < (M.take (r + L)).length by omega)
  rw [hCLTr, List.map_append, List.map_singleton] at hvalsT
  have hτL : Lc.map τ.o = Lc.map ρ'.o := List.map_congr_left (fun c hc => (hag c (by
    have hcT : c ∈ CL (M.take (r + L)) r := by rw [hCLTr]; exact List.mem_append_left _ hc
    exact (mem_children (cl_mem_children hcT)).2)).1)
  have hB : spArg (ρ.v r) z (sumN (Lc.map ρ'.o)) = t2B (ρ.v r) ρ Lc := by unfold t2B; rw [hLo]
  have hoqM : ρ.o q = psi (ρ.v q) z z := by
    rw [o_cl_eq I.cons I.good (show q < M.length by omega), TCLq]; rfl
  obtain ⟨hBc, hBot, -⟩ := leaf_M_side I (show r < M.length by omega) hCLM hoqM
  have hoqle : ρ'.o q ≤ ρ.o q := po_le (hdrop q hqx).1
  refine ⟨omega (sumN (one :: Lq.map (bumpTerm (M.take (r + L)) ρ' q))), ?_, by rw [(hag q hqT).2, hvq],
    isOT_omega (isOT_sumN _ hOT1), omega_psi_form _, ?_, ?_⟩
  · rw [hCLTr, List.map_append, List.map_singleton, hτL, (hag q hqT).1, (hag r (by omega)).2, hvr,
      sumN_append_dec hvalsT.1 hvalsT.2, sumN_singleton (hvalsT.1 _ (by simp)), spArg_app, hB, hoq,
      spArg_single, ← hvq]
    apply step_app_leaf hBot (T.not_lt_z _)
    intro hBz
    rw [← hoq]
    exact le_trans hoqle (hoqM ▸ hBc _ (last_mem_summands hBz))
  · apply omega_le_omega (isOT_sumN _ hOT1) (isOT_sumN _ hOT2)
    exact sumN_le2 (List.Forall₂.cons (le_refl _) (forall₂_map_le Lq hbT)) hOT1 hOT2
  · exact hvqM

#print axioms qn_take_t1LV3

/-- **`QNRelR3` holds**: the state of `r` in `M.take x` is `B + Ω_{V + ω_T}` and `V < V + ω_T`. -/
theorem qnRelR3_holds {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (Ctx : StepCtx3 M ρ rk) {r L q : Nat} {Lc : List Nat} (hlen : r + L + 1 = M.length)
    (hr : par M 2 (r + L) = some r) (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    (hCL : CL M r = Lc ++ [q]) : QNRelR3 M ρ r L q Lc := by
  refine ⟨fun τ hτ => ?_⟩
  obtain ⟨ωT, hst, _, _, ⟨a, b, hab⟩, _, _⟩ := qn_take_t1LV3 hM hS I Ctx hlen hr hq hqr hCL hτ
  refine ⟨add (ρ.v r) ωT, hst, ?_⟩
  rw [hab]; exact lt_add_principal a b _

/-- `SeedPFResV3R3` without the field `qn`. -/
structure SeedPFResV3R4 (M : Mat) (ρ : Valn) : Prop where
  qr : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    (∀ i, upg M i ≠ some (r + L)) → ∀ Lc, CL M r = Lc ++ [r + L] → QRRelR M ρ r L Lc
  sv : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    upg M (r + L - 1) = some (r + L) → SVRel M ρ r L
  C1 : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = none → CRelR M ρ r L q
  C2r : ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFr QPF M r L r

theorem seedPFResV3R3_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (Ctx : StepCtx3 M ρ rk) (h : SeedPFResV3R4 M ρ) : SeedPFResV3R3 M ρ :=
  ⟨h.qr, h.sv, fun r L q hlen hr hq hqr Lc hLc => qnRelR3_holds hM hS I Ctx hlen hr hq hqr hLc, h.C1, h.C2r⟩

/-- `SeedVFResV3R3` without the field `qn`. -/
structure SeedVFResV3R4 (M : Mat) (ρ : Valn) : Prop where
  pf : SeedPFResV3R4 M ρ
  qnDom : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → T2SeedQNDom M ρ r L q Lc
  cDom : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = none → T2SeedCDom M ρ r L q
  C2r : ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFr QVF M r L r

theorem seedVFResV3R3_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (Ctx : StepCtx3 M ρ rk) (h : SeedVFResV3R4 M ρ) : SeedVFResV3R3 M ρ :=
  ⟨seedPFResV3R3_of hM hS I Ctx h.pf, h.qnDom, h.cDom, h.C2r⟩

section
variable (hDI : HDropInputsV3) (hF : HFrameV3)
    (hAbsU : T0AtV3 (fun M ρ r L => T0AbsWU M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ))
    (hQR : HQRInputsStepV3) (hQN : HQNInputsV3)
    (hBXU2 : T2AtV3 (fun M ρ => T2BelowAtV3U2 M ρ))
    (hCanH2 : HCanonHard2)
    (hVF4 : T2AtV3 (fun M ρ => SeedVFResV3R4 M ρ))
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

include hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2 hVF4 hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG

/-- **Order preservation of the translation below SRO** from the current residuals (`SeedVFResV3R4`). -/
theorem translation_order_res9
    {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA :=
  translation_order_res8 hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2
    (fun M ρ rk C hz h2 => seedVFResV3R3_of C.std C.ne (coreW C.S C.I) C (hVF4 M ρ rk C hz h2))
    hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG hA hB hAS hBE hlt

/-- **Surjectivity of the translation below SRO** from the current residuals and `EvalFSNZ 2`. -/
theorem translation_surj_res9 (hFS : EvalFSNZ 2)
    {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  translation_surj_res8 hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2
    (fun M ρ rk C hz h2 => seedVFResV3R3_of C.std C.ne (coreW C.S C.I) C (hVF4 M ρ rk C hz h2))
    hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG hFS hot hvN hlt

end

#print axioms qnRelR3_holds
#print axioms translation_order_res9
#print axioms translation_surj_res9

end Ytosk.V3Main.SeedPF
