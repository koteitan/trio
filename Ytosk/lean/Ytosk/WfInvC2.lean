/-
**WfInvC2: the top with the weaker qn path clause (2026-10-31).**

`T2SeedClV2W` is `WfScout.T2SeedClV2R` with the qn field `WfInvC.T2SeedQNBaseRW` (the components of `s′` at the
path levels only below `B + Ω_{s′}`; the old `< X₁` is false, WfReM2). The bridges below rebuild everything the top
took from `T2SeedClV2B`, and `trio_terminates_main_V2_W` is `trio_terminates_main_V2_cur` with `hClR` replaced by
`hClW`. (The other hypotheses of the top are still those of `V3TopT2B`; several are known false, see redesign.md.)
-/
import Ytosk.WfInvC1
import Ytosk.V3TopT2B

namespace Ytosk.WfInvC

open T WfScout

set_option linter.unusedSectionVars false

/-- **Residual (t2): `WfScout.T2SeedClV2R` with the weaker qn path clause.** -/
def T2SeedClV2W : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      (∀ q Lc, par M 0 (r + L) = some q → q ≠ r → CL M r = Lc ++ [q] → T2SeedQNBaseRW M ρ r L q Lc) ∧
      (T2SVCase M r L → T2SeedSVBaseR M ρ r L) ∧
      (∀ q, par M 0 (r + L) = some q → q ≠ r → (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCBaseR M ρ r L q)

/-- **`T2SeedClV2B` with the weaker qn base.** -/
def T2SeedClV2BW : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      (∀ q Lc, par M 0 (r + L) = some q → q ≠ r → CL M r = Lc ++ [q] → T2SeedQNBaseW M ρ r L q Lc) ∧
      (T2SVCase M r L → T2SeedSVBase M ρ r L) ∧
      (∀ q, par M 0 (r + L) = some q → q ≠ r → (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCBase M ρ r L q)

/-- **Bridge** (the proof of `WfScout.t2SeedClV2B_of_R`; only the qn field changes). -/
theorem t2SeedClV2BW_of_W (h : T2SeedClV2W) : T2SeedClV2BW := by
  intro M ρ rk C hz h2 r L hlen hr
  obtain ⟨hQN, hSV, hCC⟩ := h M ρ rk C hz h2 r L hlen hr
  have I : Inv3W M ρ rk := Inv3W.ofV2 C.S C.I
  have R : Res3W M ρ rk := C.toW
  have hM := C.std
  have hS := C.ne
  have hrT : r < (M.take (r + L)).length := by
    have := par_lt M 2 _ _ hr; rw [List.length_take]; omega
  have hrM : r < M.length := by omega
  have hG3 : ∀ τ, Cons (M.take (r + L)) τ → Good3 (M.take (r + L)) τ := by
    intro τ hτ
    have hτ' : Cons (M.take (M.length - 1)) τ := by rw [show M.length - 1 = r + L by omega]; exact hτ
    have hG := good3_take_any I R (by omega) hτ'
    rw [show M.length - 1 = r + L by omega] at hG
    exact hG
  refine ⟨fun q Lc hq hqr hCL => ?_, fun hc => ?_, fun q hq hqr hncl => ?_⟩
  · -- qn
    intro τ hτ t1 hsp
    obtain ⟨H1, H3⟩ := hQN q Lc hq hqr hCL τ hτ t1 hsp
    have hG := hG3 τ hτ
    have hvr : τ.v r = ρ.v r :=
      v_take_of_untopped I (by omega) (par_lt M 2 _ _ hr) (topP_C hM hS I hlen hr hq hqr) hτ
    obtain ⟨ωT, hsp', -, -, -, hωT, -⟩ := qn_take_t1L hM hS I R hlen hr hq hqr hCL hτ
    have he := app_left_cancel (hsp.symm.trans hsp')
    have ht1 : t1 = add (ρ.v r) ωT := (psi.inj he).1
    have H2 : Lc = [] → t1 ≤ qnS M ρ r L q := fun _ => by
      rw [ht1]; unfold qnS; exact add_le_add_left _ hωT
    have hot := hG.ot_o r hrT
    rw [o_cl_eq hτ hG hrT, hsp, hvr] at hot
    exact ⟨hot, H1, H2, H3⟩
  · -- sv
    obtain ⟨hq, hux⟩ := hc
    intro τ hτ X hX
    obtain ⟨P, b, x, T1, hXe, hX1e, hT1, hsP, hcl⟩ := hSV ⟨hq, hux⟩ τ hτ X hX
    obtain ⟨hG, hvr, hch⟩ := sv_children_ctx hM hS I R hlen hr hq hux hτ
    obtain ⟨hX1ot, hX1V⟩ := x1_facts hτ hG hrT hvr
    have hXe' : X = spArg (ρ.v r) z (sumN ((CL M r).map ρ.o)) := by
      have h1 := o_cl_eq I.cons I.good hrM
      rw [hX] at h1
      exact (psi.inj h1).2.1
    have hchM := sv_children_M hM hS I hlen hr hq
    refine ⟨P, b, x, T1, hXe, hX1e, hT1, hsP, ?_, ?_, hX1ot, ?_⟩
    · rw [hXe']
      exact arg_summands_ge I.cons I.good (fun d hd => le_of_lt (hchM d (cl_mem_children hd)))
    · have h := arg_summands_ge hτ hG (w := succ (ρ.v r)) (i := r)
        (fun d hd => le_of_lt (hch d (cl_mem_children hd)))
      intro q hq'
      exact h q hq'
    · intro u hu hlt g hg
      rcases hu with rfl | hu
      · rcases List.mem_append.mp hg with hg | hg
        · exact hX1V g hg
        · rw [comps_self_nil (I.good.ot_v r hrM)] at hg; simp at hg
      · exact hcl u hu hlt g hg
  · -- C
    intro τ hτ X hX
    obtain ⟨P, b, x, T1, hXe, hX1e, hT1, hsP, hs3, hcV, hcl⟩ := hCC q hq hqr hncl τ hτ X hX
    have hG := hG3 τ hτ
    have hvr : τ.v r = ρ.v r :=
      v_take_of_untopped I (by omega) (par_lt M 2 _ _ hr) (topP_C hM hS I hlen hr hq hqr) hτ
    obtain ⟨hX1ot, hX1V⟩ := x1_facts hτ hG hrT hvr
    have heM := c_children_e1 hM hS I hlen hr hq hqr
    have hXe' : X = spArg (ρ.v r) z (sumN ((CL M r).map ρ.o)) := by
      have h1 := o_cl_eq I.cons I.good hrM
      rw [hX] at h1
      exact (psi.inj h1).2.1
    have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
    rw [show M.length - 1 = r + L by omega] at hcnt
    have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
    have heT : ∀ d ∈ children (M.take (r + L)) r, entry (M.take (r + L)) 1 r < entry (M.take (r + L)) 1 d := by
      intro d hd
      rw [children_take, List.mem_filter] at hd
      have hdx : d < r + L := by simpa using hd.2
      rw [entry_take M 1 hdx, entry_take M 1 (par_lt M 2 _ _ hr)]
      exact heM d hd.1
    have hs1 : ∀ q ∈ summands X, ¬ q < psi (succ (ρ.v r)) z z := by
      rw [hXe']
      exact arg_summands_ge I.cons I.good (children_v_ge I.cons I.good I.rank heM)
    have hs2 : ∀ q ∈ summands (t2X1 M r L τ), ¬ q < psi (succ (ρ.v r)) z z := by
      have h := arg_summands_ge hτ hG (children_v_ge hτ hG hRk1 heT)
      intro q' hq'
      have h' := h q' hq'
      rwa [hvr] at h'
    refine ⟨P, b, x, T1, hXe, hX1e, hT1, hsP, hs1, hs2, hs3, hX1ot, ?_⟩
    intro u hu hlt g hg
    rcases hu with rfl | hu
    · rcases List.mem_append.mp hg with hg | hg
      · exact hX1V g hg
      · exact hcV g hg
    · exact hcl u hu hlt g hg

theorem t2SeedQNOT_of_W {M : Mat} {ρ : Valn} {r L q : Nat} {Lc : List Nat} (hV : isOT (ρ.v r) = true)
    (hs : isOT (qnS M ρ r L q) = true) (hσB : sh (ρ.v r) (qnS M ρ r L q) (t2B (ρ.v r) ρ Lc) = t2B (ρ.v r) ρ Lc)
    (hVt' : ∀ τ, Cons (M.take (r + L)) τ → ∀ t1,
      spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z) → ρ.v r < t1)
    (h : T2SeedQNBaseW M ρ r L q Lc) : T2SeedQNOT M ρ r L q Lc := by
  intro τ hτ t1 ht1 k hk
  have hVt := hVt' τ hτ t1 ht1
  obtain ⟨hot, hcV, -, -⟩ := h τ hτ t1 ht1
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact ⟨(qn_ot_of hV hs (qnS_gt M ρ r L q) hσB hVt hot hcV (k' + 1)).1,
    (qn_ot_of hV hs (qnS_gt M ρ r L q) hσB hVt hot hcV k').2⟩

theorem t2SeedClV2_of_BW (h : T2SeedClV2BW) (hP : T2SeedPResV2) : T2SeedClV2 := by
  intro M ρ rk C hz h2 r L hlen hr
  obtain ⟨hQN, hSV, hCC⟩ := h M ρ rk C hz h2 r L hlen hr
  have hrM : r < M.length := by omega
  have IW := Inv3W.ofV2 C.S C.I
  exact ⟨fun q Lc hq hqr hCL =>
      have hF := qnRes_base_facts ((hP M ρ rk C hz h2).qn r L q hlen hr hq hqr Lc hCL)
      t2SeedQNCl_of_W (IW.good.ot_v r hrM) (qnS_ot IW hrM L q) hF.1 hF.2 (hQN q Lc hq hqr hCL),
    fun hc => t2SeedSVCl_of_base (IW.good.ot_v r hrM) (hSV hc),
    fun q hq hqr hncl => t2SeedCCl_of_base (IW.good.ot_v r hrM) (qnS_ot IW hrM L q) (hCC q hq hqr hncl)⟩

theorem t2SeedOTRestV2_of_BW (hCl : T2SeedClV2BW) (hP : T2SeedPResV2) : T2SeedOTRestV2 := by
  intro M ρ rk C hz h2 r L hlen hr
  obtain ⟨hQN, _, hCC⟩ := hCl M ρ rk C hz h2 r L hlen hr
  have hrM : r < M.length := by omega
  have IW := Inv3W.ofV2 C.S C.I
  refine ⟨fun q Lc hq hqr hCL =>
      have hF := qnRes_base_facts ((hP M ρ rk C hz h2).qn r L q hlen hr hq hqr Lc hCL)
      t2SeedQNOT_of_W (IW.good.ot_v r hrM) (qnS_ot IW hrM L q) hF.1 hF.2 (hQN q Lc hq hqr hCL),
    fun q hq hqr hncl τ hτ => ⟨fun k _ => ?_, ?_⟩⟩
  · exact seedCOT1_of_base (IW.good.ot_v r hrM) (qnS_ot IW hrM L q) (o_arg_form IW hrM) (hCC q hq hqr hncl) τ hτ k
  · exact seedCOT2_of_base (IW.good.ot_v r hrM) (qnS_ot IW hrM L q) (o_arg_form IW hrM) (hCC q hq hqr hncl) τ hτ

theorem t2SeedPResRCV2_of_BW (hCl : T2SeedClV2BW) (h : T2SeedPResRCV2B) : T2SeedPResRCV2 := by
  intro M ρ rk C hz h2
  have H := h M ρ rk C hz h2
  have IW := Inv3W.ofV2 C.S C.I
  refine ⟨H.qr, H.sv, fun r L q hlen hr hq hqr Lc hCL τ hτ => ?_, fun r L q hlen hr hq hqr hncl => ?_⟩
  swap
  · have hrM : r < M.length := by omega
    have HC := H.C r L q hlen hr hq hqr hncl
    obtain ⟨_, _, hCC⟩ := hCl M ρ rk C hz h2 r L hlen hr
    have hun : upg M (r + L - 1) = none := by
      by_contra hne
      exact C.good ⟨r, L, q, hlen, hr, hq, hqr, hncl, hne⟩
    exact ⟨HC.decP, hun, c_rw_of_base (IW.good.ot_v r hrM) (qnS_ot IW hrM L q) (o_arg_form IW hrM)
      (hCC q hq hqr hncl) HC.strict, HC.lhd⟩
  obtain ⟨t1, he, hVt, ht1, hk⟩ := H.qn r L q hlen hr hq hqr Lc hCL τ hτ
  have hrM : r < M.length := by omega
  have hF := tqN_facts (IW.good.ot_v r hrM) (qnS_ot IW hrM L q) (qnS_gt M ρ r L q) hVt ht1
  exact ⟨t1, he, fun k => ⟨(hF k).2.1, (hF k).2.2, hk k⟩⟩

/-- **`T2SeedQNDom` from `T2SeedQNDom1` and the weaker base** (the proof of `t2SeedQNDom_of1`; it uses only the level-`V`
field and `t₁ ≤ s′`). -/
theorem t2SeedQNDom_of1W {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3W M ρ rk) {r L q : Nat}
    {Lc : List Nat} (hlen : r + L + 1 = M.length) (h1 : T2SeedQNDom1 M ρ r L q Lc)
    (hB : T2SeedQNBaseW M ρ r L q Lc)
    (hP : ∀ τ, Cons (M.take (r + L)) τ → ∃ t1,
      spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z)) :
    T2SeedQNDom M ρ r L q Lc := by
  refine ⟨fun hL => (h1 hL).1, fun g hg => ?_⟩
  by_cases hL : Lc = []
  · subst hL
    have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
    rw [show M.length - 1 = r + L by omega] at hcnt
    have hC0 := cons_of_rk (rk_take (by omega) I.rank hcnt)
    obtain ⟨t1, ht1⟩ := hP _ hC0
    obtain ⟨-, hcV, hts, -⟩ := hB _ hC0 t1 ht1
    have hBz : app (t2B (ρ.v r) ρ []) (psi t1 z z) = psi t1 z z := rfl
    have hle : psi t1 z z ≤ psi (qnS M ρ r L q) z z := by
      rcases (le_iff _ _).mp (hts rfl) with h5 | h5
      · exact psi_le_psi_of (Or.inl h5)
      · rw [h5]
    left
    have := hcV g hg; rw [hBz] at this; exact le_trans (le_of_lt this) hle
  · rcases (h1 hL).2 (ρ.v r) (Or.inl rfl) (lt_irrefl' _) g hg with h | h | ⟨d, hd, _⟩
    · exact Or.inl h
    · exact Or.inr h
    · rw [comps_self (I.good.ot_v r (by omega))] at hd; simp at hd

theorem t2SeedDomV2_of_BW (hCl : T2SeedClV2BW) (hPB : T2SeedPResRCV2B) (h : T2SeedDomV2B) : T2SeedDomV2 := by
  intro M ρ rk C hz h2
  obtain ⟨hQ, hC1⟩ := h M ρ rk C hz h2
  refine ⟨fun r L q hlen hr hq hqr Lc hCL => ?_, fun r L q hlen hr hq hqr hncl => ?_⟩
  · exact t2SeedQNDom_of1W (Inv3W.ofV2 C.S C.I) hlen (hQ r L q hlen hr hq hqr Lc hCL)
      ((hCl M ρ rk C hz h2 r L hlen hr).1 q Lc hq hqr hCL)
      (fun τ hτ => let ⟨t1, he, _⟩ := (hPB M ρ rk C hz h2).qn r L q hlen hr hq hqr Lc hCL τ hτ; ⟨t1, he⟩)
  · exact t2SeedCDom_of (Inv3W.ofV2 C.S C.I) (by omega) (hC1 r L q hlen hr hq hqr hncl)
      ((hCl M ρ rk C hz h2 r L hlen hr).2.2 q hq hqr hncl)

/-- **The top with `hClW` in place of `hClR`.** -/
theorem trio_terminates_main_V2_W (hDU : HDropU) (hTB2 : T2BadRes) (hStep : WfB2S.B2StepAb) (hSib : WfH7W.H7WSib)
    (hF : HFrameV2) (hLf : HLeafV2)
    (hBE : HBumpExt) (hCB : T2CBadOut)
    (hVU : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → FDCopyRoot.T2VAncUse M)
    (hClW : T2SeedClV2W) (hPRE : T2SeedPResRCV2E) (hCan : HCanonV2)
    (hDomQ : T2SeedDomV2Q)
    (hVCp : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRACopyEsc M)
    (hAG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRAK KAG M) : WellFounded Step' :=
  have hCl : T2SeedClV2BW := t2SeedClV2BW_of_W hClW
  have hDW : HDropV2W := hDropV2W_of_U hDU
  have hDB : DropBadV2B := dropBadB_of_U hDU (rootBad_of_T2 hDU (rootBadV2T2_holds hDU))
  have hDomB : T2SeedDomV2B := t2SeedDomV2B_of_Q hDomQ
  have hPRB : T2SeedPResRCV2B := t2SeedPResRCV2B_of_C (t2SeedPResRCV2C_of_D (t2SeedPResRCV2D_of_E (WfH7W.t2QNDomBad_of_B2 (WfB2S.huacB2_of_ab hStep) hTB2.2) hPRE))
  have hSV0 : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
        T2SVCase M r L → T2SVc0 M ρ r L := fun M ρ rk C hz h2 r L hlen hr hc =>
    t2SVc0_of (Inv3W.ofV2 C.S C.I) hlen (t2SVc0'_of_drop C.toStepCtxB C.hdrop hlen)
  have hCF : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r →
        par M 0 (r + L) = some q → q ≠ r → (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2CFrRes M ρ r L q :=
    fun M ρ rk C hz h2 r L q hlen hr hq hqr hncl =>
      ⟨cl_C C.std C.ne (Inv3W.ofV2 C.S C.I) hlen hr hq hqr hncl
        (by by_contra hne; exact C.good ⟨r, L, q, hlen, hr, hq, hqr, hncl, hne⟩), t2SVc0_of (Inv3W.ofV2 C.S C.I) hlen
        (t2SVc0'_of_drop C.toStepCtxB C.hdrop hlen)⟩
  have hDom : T2SeedDomV2 := t2SeedDomV2_of_BW hCl hPRB hDomB
  have hQNG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r →
        par M 0 (r + L) = some q → q ≠ r → ∀ Lc, CL M r = Lc ++ [q] → T2VRAQNDom M ρ r L q Lc :=
    fun M ρ rk C hz h2 r L q hlen hr hq hqr Lc hCL =>
      t2VRAQNDom_of (fun hL => ((hDomB M ρ rk C hz h2).1 r L q hlen hr hq hqr Lc hCL hL).2)
        (fun hL => by
          subst hL
          exact t2VRAQNDom0_of_W (Inv3W.ofV2 C.S C.I) hlen
            ((hCl M ρ rk C hz h2 r L hlen hr).1 q [] hq hqr hCL)
            (fun τ hτ => let ⟨t1, he, _⟩ := (hPRB M ρ rk C hz h2).qn r L q hlen hr hq hqr [] hCL τ hτ; ⟨t1, he⟩))
  have hPR : T2SeedPResRCV2 := t2SeedPResRCV2_of_BW hCl hPRB
  have hPRV : T2SeedPResRV2 := t2SeedPResR_of_canon hCan hPR
  have hP : T2SeedPResV2 := t2SeedPResV2_of hPRV
  have hBX : T2BelowXResV2 := t2BelowXResV2_of (WfT2Exp.t2BelowRV2_of_src hP (t2SeedClV2_of_BW hCl hP) (t2BumpMonoV2_of_ext hBE) (WfT2Src.t2AbsNSrc_of_W (WfSrcR5.t2AbsNSrcW_of hTB2.1.1 (WfTerm.aTerm_of hTB2.1.2.1) (WfTerm.bTerm_of hTB2.1.2.1) hTB2.1.2.2))) hP (t2SeedOTV2_of hP (t2SeedOTRestV2_of_BW hCl hP))
  have hVPrC : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2SeedPreShapeC M ρ := fun M ρ rk C hz h2 =>
    t2SeedPreShapeC_of (hBX M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2 (hP M ρ rk C hz h2)
      (hCF M ρ rk C hz h2)
  have hVPr : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2SeedPreShapeSVC M ρ := fun M ρ rk C hz h2 =>
    t2SeedPreShapeSVC_of (hBX M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2
      (hSV0 M ρ rk C hz h2) (hVPrC M ρ rk C hz h2)
  have hSVCG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRASeedSVC M := fun M ρ rk C hz h2 =>
    t2VRASeedSVC_of (hBX M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2 C.I.vra
      (t2VRAPre_of (hBX M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2
        (t2SeedPreShape_of C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2 (hVPr M ρ rk C hz h2)))
      (hSV0 M ρ rk C hz h2)
      (t2VRASeedC_of (hBX M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2 C.I.vra
        (t2VRAPre_of (hBX M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2
          (t2SeedPreShape_of C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2 (hVPr M ρ rk C hz h2)))
        (hP M ρ rk C hz h2) (hCF M ρ rk C hz h2)
        (fun r L q hlen hr hq hqr hncl => (hCl M ρ rk C hz h2 r L hlen hr).2.2 q hq hqr hncl))
  have hPreG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRAPre M ρ := fun M ρ rk C hz h2 =>
    t2VRAPre_of (hBX M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2
      (t2SeedPreShape_of C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2 (hVPr M ρ rk C hz h2))
  have hFD : T2FDCopyRes := FDCopyRoot.t2FDCopyRes_of_path hBX (t2FOSeedV2_of hP hDom) hVU hAG
  have hE2 : ExpT2V2 := expT2V2_of hBX (t2FOSeedV2_of hP hDom) hP (t2VSFCV2_of2 hBX hFD hP hDom)
    (t2VRAV2_of qVRAshK_KVRA hBX (t2VRASeedG_of hBX hP hPreG hQNG hSVCG) hPreG hVCp
      (fun M ρ rk C hz h2 => t2VRAK_KVRA_of (hVU M ρ rk C hz h2).vdom (hAG M ρ rk C hz h2))) hF hLf
  have hBR : BadOutT2B := badOutT2B_of hDU (hDropV2_of' hDW) (hTake_of_glob hF hLf)
    (takeBad_of_drop (dropBad_of_B hDB) hF hLf) hE2 (r2V2_of hBX) hCB
  trio_terminates_main_V2_base hDU (hDropV2_of' hDW) (takeBad_of_drop (dropBad_of_B hDB) hF hLf)
    (badOutV2_of (badOutT0_of hDU hBE (takeBad_of_drop (dropBad_of_B hDB) hF hLf) hF hLf (t0BadSeeds_of hDU (t0BadSeedsH_of hDU (t0BadSeedsH2_of hDU hBE (t0BadSeedsH3_of hDU (t0BadSeedsH4_of hDU hBE (t0BadSeedsH5_of hDU (t0BadSeedsH6_of_W (WfH7W.t0BadSeedsH7W_of_sib hDU (WfB2S.huacB2_of_ab hStep) hSib))))))))) (badOutRest_of (badOutT12_of hDU (takeBad_of_drop (dropBad_of_B hDB) hF hLf) hF hLf hBR))) hF hLf
    (t0AbWRes_of_ext (hDropV2_of' hDW) hBE)
    hCB hBX
    hPRV hDom hFD hQNG hSVCG
    (fun M ρ rk C hz h2 => t2SeedPreShape_of C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2 (hVPr M ρ rk C hz h2))
    hVCp (fun M ρ rk C hz h2 => t2VRAK_KVRA_of
      (hVU M ρ rk C hz h2).vdom
      (hAG M ρ rk C hz h2))


/-- **The old residual gives the new one** (`t₁ ≤ s′` by `qn_take_t1L`, so `X₁ ≤ B + Ω_{s′}`). -/
theorem t2SeedClV2W_of_R (h : T2SeedClV2R) : T2SeedClV2W := by
  intro M ρ rk C hz h2 r L hlen hr
  obtain ⟨hQN, hSV, hCC⟩ := h M ρ rk C hz h2 r L hlen hr
  refine ⟨fun q Lc hq hqr hCL => ?_, hSV, hCC⟩
  intro τ hτ t1 hsp
  obtain ⟨H1, H3⟩ := hQN q Lc hq hqr hCL τ hτ t1 hsp
  have I : Inv3W M ρ rk := Inv3W.ofV2 C.S C.I
  obtain ⟨ωT, hsp', -, -, -, hωT, -⟩ := qn_take_t1L C.std C.ne I C.toW hlen hr hq hqr hCL hτ
  have he := app_left_cancel (hsp.symm.trans hsp')
  have ht1 : t1 = add (ρ.v r) ωT := (psi.inj he).1
  have hts : t1 ≤ qnS M ρ r L q := by rw [ht1]; unfold qnS; exact add_le_add_left _ hωT
  have hle : app (t2B (ρ.v r) ρ Lc) (psi t1 z z) ≤ app (t2B (ρ.v r) ρ Lc) (psi (qnS M ρ r L q) z z) := by
    rcases (le_iff _ _).mp hts with h5 | h5
    · exact le_of_lt (app_lt_app_left _ (psi_lt_psi_z_iff.mpr (Or.inl h5)))
    · rw [h5]
  exact ⟨H1, fun u hu hVu => ⟨fun g hg => H3 u hu hVu g (List.mem_append_left _ hg),
    fun g hg => lt_of_lt_of_le (H3 u hu hVu g (List.mem_append_right _ hg)) hle⟩⟩

#print axioms trio_terminates_main_V2_W
#print axioms t2SeedClV2W_of_R

end Ytosk.WfInvC
