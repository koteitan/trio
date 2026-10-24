/-
**今の最上位の定理（2026-10-17、t2・top）。**

`trio_terminates_main_V2_base`（V3TopV2）の仮定 `T2BelowXResV2` を `t2BelowXResV2_of`（V3T2BelowV2）で埋め、
x より前の残り `T2BelowRV2` を `t2BelowRV2_of`（V3T2BelowR）で、種の標準形 `T2SeedOTV2` を `t2SeedOTV2_of`
（V3T2SeedOTP）で、種の列の枠の形 `T2SeedPreShape` を `t2SeedPreShape_of`（V3T2SeedPre）で小さい残りに替える。
影の枠の閉じ方は G3 の切り口の形（PH3cG）と段を限った種の上限から（V3CutClosed の `shadow_hShL_from_kind`、2026-10-18）。残り HRwClL は外した。種の残りは `T2SeedPResRCV2` と、兄弟の値の条件 `HSibColV2`（V3SibCol の SibColW）から。
最上位はこのファイルの `trio_terminates_main_V2_cur` 1 本。
-/
import Ytosk.V3TopV2
import Ytosk.V3SibCol
import Ytosk.V3T2BelowV2
import Ytosk.V3T2BelowR
import Ytosk.V3T2SeedPre
import Ytosk.V3T2SeedOTP
import Ytosk.V3BumpExt
import Ytosk.V3T2SeedSVCl
import Ytosk.V3T2VRASV
import Ytosk.V3T2SeedQNK
import Ytosk.V3CDomH
import Ytosk.V3QNTakeL
import Ytosk.V3QNDropV
import Ytosk.V3VAncPos
import Ytosk.V3SibCanonTop
import Ytosk.V3FDCopyRoot
import Ytosk.V3T0BadOut

namespace Ytosk

/-- **The sibling value condition `SibColU` of every standard matrix** (replaces `HSibHardV2`; two counted
children are covered by `Good3.dec`, two bump children by `v_bump_sib`). -/
def HSibColV2 : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Rk N rk → Good3 N σ → SibColU N σ

theorem hSibHard_of_col (h : HSibColV2) : HSibHardV2 := fun N σ rk hN hS hC hR hG =>
  upgSibVHard_of_col (sInvXJ_std hN hS).1 (sInvXJ_std hN hS).2 hC hR hG
    (sibColW_of_U (sInvXJ_std hN hS).1 hC hG (h N σ rk hN hS hC hR hG))

/-- **The current top theorem.** The hypotheses are the named residuals:
drop `HDropV2W` (the seed condition `HSeedV2` follows from `◁`, `SeedComps.seed_comps_lt`, 2026-10-21; the strong absorption at `t = 0` `T0UpgAbsV2` is no longer needed, 2026-10-20); shared `HFrameV2`・`HLeafV2`; t0 uses node Lhd and RClaimU instead of the former `T0ArgBRes`; the bump monotonicity along prefixes `HBumpExt` (gives t0's `T0AbWRes` and t2's `T2BumpMonoV2`); `T2VAncUse` (what the copy frames use of `VAnc`: `VDomF` at the guarded copy frames with a counted child and `VAnc` on the root edge `r → r + L` of `M[n]`, 2026-10-24; the former `HVAncStd`/`T2VAncStep` (`VAncStep` of every `M[n]`) is false on standard matrices, see desc; with `T2VRAK KAG` it gives the frame condition `KVRA`);
t2 the closedness of the seed argument `T2SeedClV2B` (qn, and the `k`-free sv・C parts `T2SeedSVBase`・`T2SeedCBase`),
(the seed standard forms come from `T2SeedClV2B`), the seed residual `T2SeedPResRCV2E` (qr, sv and C; the qn field is proved, 2026-10-23: `qn_take_t1L`・`qn_tqN_lhd`・`qn_drop_v_noupg`・`qn_drop_v_upg`), `T2SeedDomV2Q` (the qn part of `T2SeedDomV2B`; its C part `T2SeedCDom1` is proved, `t2SeedCDom1_holds`, 2026-10-22), `T2FDCopyRes` (the `σ`-invariance of FrameDom at the copy frames) is proved by `FDCopyRoot.t2FDCopyRes_of_path` from `T2VAncUse` and the path `T2VRAK KAG` (no residual since 2026-10-20; the pure `FDsh` is false, `FDCut.not_FDsh`),
the seed columns (qn from `T2SeedDomV2` and `T2SeedQNBase`; the last child `c₀` from the drop lemma, C: `cl_C`; no residual), the prefix shape of the seed frames (from `T2SVc0`・`T2CFrRes`), the copy levels `T2VRACopyEsc` (level provenance only for components above the child Omega and target state; the former `T2VRACopy` is false); t1 the `σ`-step at the guarded copy frames
`T2VRAK KAG` (with `T2VAncUse.vdom` it gives the frame condition `KVRA` of `qVRAshK_KVRA`); top `HCanonV2` (`CanonicalNeed`: the special case of `SibColU` that the seeds use, 2026-10-24; the former `HSibColV2` asked `SibColU` everywhere). 
2026-10-24 (the grafted bad shape `Bad2`: `x − 1` has an upgrade target, its parent is the bump child of `g`, and
either the strong absorption at `x − 1` fails while `x` lies under `g` or has row 2 ≠ 0, or `x` is the child of
`x − 1` with row 1 ≠ 0; the absorption field `UpgAbsXW0` carries `NBParX` in place of `NBPar`): the drop
residual `HDropV2W` and the engines' step context assume `¬ Bad2 M`, the frame fields `TPLoW`・`AbsDW` of `Inv3V2`
and `HFrameV2` are guarded by `¬ Bad2`; the `Bad2` matrices are the new residuals `TakeBadV2` (the one-column drop:
`Inv3V2` and the root strictly drops) and `BadOutV2` (the step for `n ≥ 2`: `Inv3V2` of `M[n]` and the descent); the
descents to `M[0]`, `M[1]` (also through a `Bad2` prefix) are proved from the prefix chain (`root_chain_of_pre`). Measured on the grafted standard sets graftA・graftB (desc).
2026-10-25: `BadOutV2` is split by the shape of the expansion: `t = 0` is proved (`badOutT0_of`, V3T0BadOut) from the
engine run on the drop's conclusion (V3T0Bad) and the new residual `T0BadSeeds` (the weak absorption and the seeds
S1・S2・S3 of `M[n]`); the rest is the residual `BadOutRest`. -/
theorem trio_terminates_main_V2_cur (hDU : HDropU) (hRB : RootBadV2T2) (hBR : BadOutRest) (hT0S : T0BadSeeds)
    (hF : HFrameV2) (hLf : HLeafV2)
    (hBE : HBumpExt) (hCB : T2CBadOut)
    (hVU : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → FDCopyRoot.T2VAncUse M)
    (hCl : T2SeedClV2B) (hPRE : T2SeedPResRCV2E) (hCan : HCanonV2)
    (hDomQ : T2SeedDomV2Q)
    (hVCp : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRACopyEsc M)
    (hAG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRAK KAG M) : WellFounded Step' :=
  have hDW : HDropV2W := hDropV2W_of_U hDU
  have hDB : DropBadV2B := dropBadB_of_U hDU (rootBad_of_T2 hDU hRB)
  have hDomB : T2SeedDomV2B := t2SeedDomV2B_of_Q hDomQ
  have hPRB : T2SeedPResRCV2B := t2SeedPResRCV2B_of_C (t2SeedPResRCV2C_of_D (t2SeedPResRCV2D_of_E hPRE))
  have hSV0 : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
        T2SVCase M r L → T2SVc0 M ρ r L := fun M ρ rk C hz h2 r L hlen hr hc =>
    t2SVc0_of (Inv3W.ofV2 C.S C.I) hlen (t2SVc0'_of_drop C.toStepCtxV2
      (hDropV2_of' hDW M ρ rk C.std C.ne (by intro h; rw [h] at hlen; simp at hlen) C.nb2 C.I) hlen)
  have hCF : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r →
        par M 0 (r + L) = some q → q ≠ r → (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2CFrRes M ρ r L q :=
    fun M ρ rk C hz h2 r L q hlen hr hq hqr hncl =>
      ⟨cl_C C.std C.ne (Inv3W.ofV2 C.S C.I) hlen hr hq hqr hncl
        (by by_contra hne; exact C.good ⟨r, L, q, hlen, hr, hq, hqr, hncl, hne⟩), t2SVc0_of (Inv3W.ofV2 C.S C.I) hlen
        (t2SVc0'_of_drop C.toStepCtxV2
          (hDropV2_of' hDW M ρ rk C.std C.ne (by intro h; rw [h] at hlen; simp at hlen) C.nb2 C.I) hlen)⟩
  have hDom : T2SeedDomV2 := t2SeedDomV2_of_B hCl hPRB hDomB
  have hQNG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r →
        par M 0 (r + L) = some q → q ≠ r → ∀ Lc, CL M r = Lc ++ [q] → T2VRAQNDom M ρ r L q Lc :=
    fun M ρ rk C hz h2 r L q hlen hr hq hqr Lc hCL =>
      t2VRAQNDom_of (fun hL => ((hDomB M ρ rk C hz h2).1 r L q hlen hr hq hqr Lc hCL hL).2)
        (fun hL => by
          subst hL
          exact t2VRAQNDom0_of (Inv3W.ofV2 C.S C.I) hlen
            ((hCl M ρ rk C hz h2 r L hlen hr).1 q [] hq hqr hCL)
            (fun τ hτ => let ⟨t1, he, _⟩ := (hPRB M ρ rk C hz h2).qn r L q hlen hr hq hqr [] hCL τ hτ; ⟨t1, he⟩))
  have hPR : T2SeedPResRCV2 := t2SeedPResRCV2_of_B hCl hPRB
  have hPRV : T2SeedPResRV2 := t2SeedPResR_of_canon hCan hPR
  have hP : T2SeedPResV2 := t2SeedPResV2_of hPRV
  have hBX : T2BelowXResV2 := t2BelowXResV2_of (t2BelowRV2_of hP (t2SeedClV2_of_B hCl hP) (t2BumpMonoV2_of_ext hBE)) hP (t2SeedOTV2_of hP (t2SeedOTRestV2_of_B hCl hP))
  have hVPrC : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2SeedPreShapeC M ρ := fun M ρ rk C hz h2 =>
    t2SeedPreShapeC_of (hBX M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ hz h2 (hP M ρ rk C hz h2)
      (hCF M ρ rk C hz h2)
  have hVPr : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2SeedPreShapeSVC M ρ := fun M ρ rk C hz h2 =>
    t2SeedPreShapeSVC_of (hBX M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ hz h2
      (hSV0 M ρ rk C hz h2) (hVPrC M ρ rk C hz h2)
  have hSVCG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRASeedSVC M := fun M ρ rk C hz h2 =>
    t2VRASeedSVC_of (hBX M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ hz h2 C.I.vra
      (t2VRAPre_of (hBX M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ hz h2
        (t2SeedPreShape_of C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ hz h2 (hVPr M ρ rk C hz h2)))
      (hSV0 M ρ rk C hz h2)
      (t2VRASeedC_of (hBX M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ hz h2 C.I.vra
        (t2VRAPre_of (hBX M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ hz h2
          (t2SeedPreShape_of C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ hz h2 (hVPr M ρ rk C hz h2)))
        (hP M ρ rk C hz h2) (hCF M ρ rk C hz h2)
        (fun r L q hlen hr hq hqr hncl => (hCl M ρ rk C hz h2 r L hlen hr).2.2 q hq hqr hncl))
  trio_terminates_main_V2_base (hDropV2_of' hDW) (takeBad_of_drop (dropBad_of_B hDB) hF hLf)
    (badOutV2_of (badOutT0_of hDU (takeBad_of_drop (dropBad_of_B hDB) hF hLf) hF hLf hT0S) hBR) hF hLf
    (t0AbWRes_of_ext (hDropV2_of' hDW) hBE)
    hCB hBX
    hPRV hDom (FDCopyRoot.t2FDCopyRes_of_path hBX (t2FOSeedV2_of hP hDom) hVU hAG) hQNG hSVCG
    (fun M ρ rk C hz h2 => t2SeedPreShape_of C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ hz h2 (hVPr M ρ rk C hz h2))
    hVCp (fun M ρ rk C hz h2 => t2VRAK_KVRA_of
      (hVU M ρ rk C hz h2).vdom
      (hAG M ρ rk C hz h2))

end Ytosk
