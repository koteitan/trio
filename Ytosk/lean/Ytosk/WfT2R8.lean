/-
**WfT2R8: the top theorem with `T2BelowXResV2X` (2026-11-01, t = 2 Bad2 route).**

`trio_terminates_main_V2_baseXR`: `trio_terminates_main_V2_base` (V3TopV2) with `hB : T2BelowXResV2X`; every
consumer of `hB` is the X copy (WfT2R1〜R7), `R2V2` is `R2V2X` (`r2V2_ofXR`) and the drop for `n ≥ 2` is
`T2Drop2X` (`t2Drop2X_of`).
`trio_terminates_main_V2_curXR`: `trio_terminates_main_V2_cur` (V3TopT2B) with `hBX` built by
`WfT2X.t2BelowXResV2X_of` from `WfT2X.T2BelowRV2X` (fields `AbsWNx`・`NotBumpKidX` in place of the false `AbsWN`),
so the hypothesis `T2BadRes` (whose first part `SrcC3Res` is false) is replaced by its second part `T2QNDomBad2`
and `WfT2X.T2BelowRV2X`.
-/
import Ytosk.WfT2R7

namespace Ytosk
open T Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The top theorem before the split of `T2BelowXRes`** (the single current form is `trio_terminates_main_V2_curXR`, V3TopT2B): everything committed so far plugged in. The hypotheses are the named
residuals: drop `HDropV2` (`HSeedV2` is no longer needed, `SeedComps.seed_comps_lt`); shared `HFrameV2`・`HLeafV2`; t0 `T0RwRes`・`T0AbWRes`;
t2 `T2BelowXRes`・`T2SeedPResRCV2`・`T2SeedDomV2`・`T2FDCopyRes`・the seed columns (`T2VRAQNDom`・`T2VRASeedSVC`)・
the prefix shape `T2SeedPreShape`・the copy levels `T2VRACopyEsc` (level provenance only for components above the child Omega and target state; the former `T2VRACopy` is false)・the `σ`-step at the guarded copy frames
`T2VRAK KVRA` (t1, the frame condition of `qVRAshK_KVRA`); top `HSibHardV2`.
None of them is the false strong absorption `HAbSV2`. (2026-10-17, drop: also `T2UpgAbsW`, the strong `UpgAbsX`
at the last column for `t = 2`, which the drop lemma no longer gives. The `t = 1` analogue `T1UpgQRV2` is removed:
t1 handles the weak seed with `SmallSelf` in `qr_final3`.) -/
theorem trio_terminates_main_V2_baseXR (hU : HDropU) (hD : HDropV2) (hTB : TakeBadV2) (hBO : BadOutV2)
    (hF : HFrameV2) (hLf : HLeafV2)
    (hAbW : T0AbWRes) (hCB : T2CBadOut)
    (hB : WfT2X.T2BelowXResV2X) (hPRV : T2SeedPResRV2) (hDom : T2SeedDomV2)
    (hFD : T2FDCopyRes)
    (hQNG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r →
        par M 0 (r + L) = some q → q ≠ r → ∀ Lc, CL M r = Lc ++ [q] → T2VRAQNDom M ρ r L q Lc)
    (hSVCG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRASeedSVC M)
    (hVPr : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2SeedPreShape M ρ)
    (hVCp : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRACopyEsc M)
    (hVK : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRAK KVRA M) : WellFounded Step' :=
  have hP : T2SeedPResV2 := t2SeedPResV2_of hPRV
  have hPreG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRAPre M ρ := fun M ρ rk C hz h2 =>
    t2VRAPre_ofXR (hB M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2 (hVPr M ρ rk C hz h2)
  terminates_of_desc3 (desc3_V2OXR hU hD (hTake_of_glob hF hLf) hTB hBO
    (expT0Out_of4 hAbW (t0Leaf_of_glob hLf) (t0Frame_of_glob hF))
    (expT1Out_V2_glob hF hLf)
    (expT2V2_ofXR hB (t2FOSeedV2_of hP hDom) hP (t2VSFCV2_of2XR hB hFD hP hDom)
      (t2VRAV2_ofXR qVRAshK_KVRA hB (t2VRASeedG_ofXR hB hP hPreG hQNG hSVCG) hPreG hVCp hVK) hF hLf)
    (r2V2_ofXR hB) (t2Drop2X_of hB) hCB)

end Ytosk

namespace Ytosk
open T Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The current top theorem.** The hypotheses are the named residuals:
drop `HDropV2W` (the seed condition `HSeedV2` follows from `◁`, `SeedComps.seed_comps_lt`, 2026-10-21; the strong absorption at `t = 0` `T0UpgAbsV2` is no longer needed, 2026-10-20); shared `HFrameV2`・`HLeafV2`; t0 uses node Lhd and RClaimU instead of the former `T0ArgBRes`; the bump monotonicity along prefixes `HBumpExt` (gives t0's `T0AbWRes` and t2's `T2BumpMonoV2`); `T2VAncUse` (what the copy frames use of `VAnc`: `VDomF` at the guarded copy frames with a counted child and `VAnc` on the root edge `r → r + L` of `M[n]`, 2026-10-24; the former `HVAncStd`/`T2VAncStep` (`VAncStep` of every `M[n]`) is false on standard matrices, see desc; with `T2VRAK KAG` it gives the frame condition `KVRA`);
t2 the closedness of the seed argument `T2SeedClV2B` (qn, and the `k`-free sv・C parts `T2SeedSVBase`・`T2SeedCBase`),
(the seed standard forms come from `T2SeedClV2B`), the seed residual `T2SeedPResRCV2E` (qr, sv and C; the qn field is proved, 2026-10-23: `qn_take_t1L`・`qn_tqN_lhd`・`qn_drop_v_noupg`・`qn_drop_v_upg`), `T2SeedDomV2Q` (the qn part of `T2SeedDomV2B`; its C part `T2SeedCDom1` is proved, `t2SeedCDom1_holds`, 2026-10-22), `T2FDCopyRes` (the `σ`-invariance of FrameDom at the copy frames) is proved by `FDCopyRoot.t2FDCopyRes_of_pathXR` from `T2VAncUse` and the path `T2VRAK KAG` (no residual since 2026-10-20; the pure `FDsh` is false, `FDCut.not_FDsh`),
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
engine run on the drop's conclusion (V3T0Bad) and the new residual `T0BadSeeds` (the seeds S1・S2・S3 of `M[n]`, narrowed to `T0BadSeedsH` by `t0BadSeeds_of`: for `r = x − 1` S1 and S2
are proved, V3T0BadSeed; then to `T0BadSeedsH2` by `t0BadSeedsH_of`: the node S1 for `r ≠ x − 1` follows from the
structural fact that `r` still counts at `g` in `M[n]` (`weak_seed_hi` for `v(r) > v(g)`, V3T0BadNode); then to `T0BadSeedsH3` by `t0BadSeedsH2_of`: S3
follows from the `M`-level sum `omid + o′(r) ◁ o(r)` (`t0_S3W`, V3T0BadS3), and that from the component fact of the weak leaf
(`T0BadSeedsH4`, `lhd_sum_weak`: every component of `w′ = v′(r)` is `0` or below a component of `v(r)`); S2 likewise from the `M`-level sum `ω^{G0} + ω^{G0′} ◁ ω^{G0 + 1}` (`T0BadSeedsH5`, `t0_S2GW`,
V3T0BadS2), and that from a component fact of `ω^{G0′}` (`T0BadSeedsH6`, `lhd_sum_dom`); the counted fact of the
first copy root reduces to `r − 1` not upgrading to `r` (`T0BadSeedsH7`, `counted_first0G`, V3T0BadCnt); the weak absorption from
`HDropU`, whose `BumpAbsC` now also covers `t = 0`, and `HBumpExt`); the rest is the residual `BadOutRest`.
2026-10-25: `BadOutRest` is proved: `t = 1` by `badOutT1`, `t = 2` by `badOutT2B_ofXR` (the step context `StepCtxB` drops
`¬ Bad2`; the `t = 2` engines run on it). The two facts the `t = 2` engines took from the old drop residual are the
`Bad2` residual `T2BadRes`: `AbsWN M M[n]` (`T2AbsNBad`; the drop side `AbsWN M (M.take x)` is false on `Bad2`) and the
first qn subscript `t_1 ◁ v_M(q)` (from the component bound `T2QNDomBad`; the drop `v_T(q) ⊴ v_M(q)` is false on `Bad2`).
2026-10-26: the general residual `HUAC` (V3HUAC: the components of `v(P₁ n)` are bounded by those of `v(n)` when `n`
upgrades to an ancestor) proves the lost-upgrade cases: `T0BadSeedsH7` from `T0BadSeedsH8` (`t0BadSeedsH7_of`) and
`T2QNDomBad` from `T2QNDomBad2` (`t2QNDomBad_of`, V3QNDomS), the narrowed residuals asserting only the shapes that do
not occur weakly on the sets.
2026-10-27: H8's first field follows strongly from the drop conclusion (T0SeedOutside.seed_lhd_outside).
2026-10-27: HUAC also proves the second field (T0SeedSum.seed_sum_lhd).
The top keeps the preceding-upgrade exclusion only when entry1(g) >= 2,
as T0H10Core.T0BadSeedsH10Big. The small case follows from structural lemmas.
2026-10-29: HUACShapes.HUACShape is false (WfHUACShapeFalse.not_HUACShape, a standard 48-column matrix).
WfHUACDeep.hUAC_of_deep derives HUAC from a zero head, a return grandchild, or a deep row-1 return
(DeepWitness) at dangerous absorption. 2026-10-29: the structural part of DeepWitness is proved (WfHUAC2Canon.canon_struct); only the value
residual WfHUAC2Canon.HUACStep (StepDom under Danger) remains for HUAC.
2026-10-29: T0H10Core.T0BadSeedsH10Big is false on a standard Bad2 matrix (WfH10Cex.h10_core_false
refutes it without its Inv3V2 premise; that premise is checked only numerically). It is removed:
its only consumer t0_S1N_cnt (V3T0BadNode) is redesigned. For v(r) > v(g) the node lemma t0_S1AW_nodeHi now
allows no counted middle copy (m = 0: the old frame does not rewrite, t0IVResC_holds, so the copies-only state is a
prefix of the old argument); for v(r) <= v(g) an upgrade r - 1 -> r is impossible (v_par0_lt_of_upg_prev), so
counted_first0G gives the count. The component fields come from HDropU and HUAC alone
(WfH10b.t0BadSeedsH7W_of, t0BadSeedsH6_of_W).
2026-10-29: WfStepHUACStepFalse.not_HUACStep refutes HUACStep (standard 39-column matrix); StepFacts3 is false too
(StepFacts3False.not_StepFacts3, standard 40-column matrix). HUAC itself is false on a standard 32-column matrix (codex, 2026-10-29).
The top therefore takes HUAC's two consumers' needs directly: T2QNDomBad (second field of T2BadRes) and
T0BadSeedsH7W (WfH10b.t0BadSeedsH7W_of derives it from HDropU and the false HUAC; it is now a residual). T2BadRes's first field is WfT2Src.T2AbsNSrcW (structural facts at
a failed drop absorption proved, src_facts). hCl is WfScout.T2SeedClV2R (the isOT, level-V and summand-bound
fields proved).
The count is 14.
2026-10-31: T0BadSeedsH7W and T2QNDomBad need HUAC only at x - 1 of a Bad2 matrix (`WfH7W.HUACB2`), plus
`WfH7W.H7WSib` (the preceding sibling in the lost-tail frame is a copy of x - 1) and `T2QNDomBad2`. T2AbsNSrcW is split
into (a), (b), (c). The count is 15 hypotheses (T2BadRes holds 4 parts).
Round 5: HUACB2 is narrowed to `WfH7W2.B2Step` (StepDom under Bad2; `WfH7W2.huacB2_of_step`). T2BadRes holds 5 parts.
Round 6: B2Step is FALSE (WfB2SFalse.not_B2Step_of, 28-column standard Bad2); replaced by the weaker `WfB2S.B2StepAb`
(j = the last bump child with children). ATerm/BTerm narrowed to `WfTerm.TermHi`.
WARNING (round 6): `WfSrcC2.SrcC3Res` is false in its core form, and so are T2AbsNSrc (c), T2AbsNBad and
`AbsWN M M[2]` (WfSrcC3Cex, standard 36-column Bad2 matrix). The Bad2 t = 2 route through `T2BelowRV2` needs a redesign. -/
theorem trio_terminates_main_V2_curXR (hDU : HDropU) (hQD : T2QNDomBad2) (hRX : WfT2X.T2BelowRV2X) (hStep : WfB2S.B2StepAb) (hSib : WfH7W.H7WSib)
    (hF : HFrameV2) (hLf : HLeafV2)
    (hBE : HBumpExt) (hCB : T2CBadOut)
    (hVU : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → FDCopyRoot.T2VAncUse M)
    (hClR : WfScout.T2SeedClV2R) (hPRE : T2SeedPResRCV2E) (hCan : HCanonV2)
    (hDomQ : T2SeedDomV2Q)
    (hVCp : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRACopyEsc M)
    (hAG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRAK KAG M) : WellFounded Step' :=
  have hCl : T2SeedClV2B := WfScout.t2SeedClV2B_of_R hClR
  have hDW : HDropV2W := hDropV2W_of_U hDU
  have hDB : DropBadV2B := dropBadB_of_U hDU (rootBad_of_T2 hDU (rootBadV2T2_holds hDU))
  have hDomB : T2SeedDomV2B := t2SeedDomV2B_of_Q hDomQ
  have hPRB : T2SeedPResRCV2B := t2SeedPResRCV2B_of_C (t2SeedPResRCV2C_of_D (t2SeedPResRCV2D_of_E (WfH7W.t2QNDomBad_of_B2 (WfB2S.huacB2_of_ab hStep) hQD) hPRE))
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
  have hBX : WfT2X.T2BelowXResV2X := WfT2X.t2BelowXResV2X_of hRX hP (t2SeedOTV2_of hP (t2SeedOTRestV2_of_B hCl hP))
  have hVPrC : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2SeedPreShapeC M ρ := fun M ρ rk C hz h2 =>
    t2SeedPreShapeC_ofXR (hBX M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2 (hP M ρ rk C hz h2)
      (hCF M ρ rk C hz h2)
  have hVPr : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2SeedPreShapeSVC M ρ := fun M ρ rk C hz h2 =>
    t2SeedPreShapeSVC_ofXR (hBX M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2
      (hSV0 M ρ rk C hz h2) (hVPrC M ρ rk C hz h2)
  have hSVCG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRASeedSVC M := fun M ρ rk C hz h2 =>
    t2VRASeedSVC_ofXR (hBX M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2 C.I.vra
      (t2VRAPre_ofXR (hBX M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2
        (t2SeedPreShape_of C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2 (hVPr M ρ rk C hz h2)))
      (hSV0 M ρ rk C hz h2)
      (t2VRASeedC_ofXR (hBX M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2 C.I.vra
        (t2VRAPre_ofXR (hBX M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2
          (t2SeedPreShape_of C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2 (hVPr M ρ rk C hz h2)))
        (hP M ρ rk C hz h2) (hCF M ρ rk C hz h2)
        (fun r L q hlen hr hq hqr hncl => (hCl M ρ rk C hz h2 r L hlen hr).2.2 q hq hqr hncl))
  have hPreG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRAPre M ρ := fun M ρ rk C hz h2 =>
    t2VRAPre_ofXR (hBX M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2
      (t2SeedPreShape_of C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2 (hVPr M ρ rk C hz h2))
  have hFD : T2FDCopyRes := FDCopyRoot.t2FDCopyRes_of_pathXR hBX (t2FOSeedV2_of hP hDom) hVU hAG
  have hE2 : ExpT2V2 := expT2V2_ofXR hBX (t2FOSeedV2_of hP hDom) hP (t2VSFCV2_of2XR hBX hFD hP hDom)
    (t2VRAV2_ofXR qVRAshK_KVRA hBX (t2VRASeedG_ofXR hBX hP hPreG hQNG hSVCG) hPreG hVCp
      (fun M ρ rk C hz h2 => t2VRAK_KVRA_of (hVU M ρ rk C hz h2).vdom (hAG M ρ rk C hz h2))) hF hLf
  have hBR : BadOutT2B := badOutT2B_ofXR hDU (hDropV2_of' hDW) (hTake_of_glob hF hLf)
    (takeBad_of_drop (dropBad_of_B hDB) hF hLf) hE2 (r2V2_ofXR hBX) (t2Drop2X_of hBX) hCB
  trio_terminates_main_V2_baseXR hDU (hDropV2_of' hDW) (takeBad_of_drop (dropBad_of_B hDB) hF hLf)
    (badOutV2_of (badOutT0_of hDU hBE (takeBad_of_drop (dropBad_of_B hDB) hF hLf) hF hLf (t0BadSeeds_of hDU (t0BadSeedsH_of hDU (t0BadSeedsH2_of hDU hBE (t0BadSeedsH3_of hDU (t0BadSeedsH4_of hDU hBE (t0BadSeedsH5_of hDU (t0BadSeedsH6_of_W (WfH7W.t0BadSeedsH7W_of_sib hDU (WfB2S.huacB2_of_ab hStep) hSib))))))))) (badOutRest_of (badOutT12_of hDU (takeBad_of_drop (dropBad_of_B hDB) hF hLf) hF hLf hBR))) hF hLf
    (t0AbWRes_of_ext (hDropV2_of' hDW) hBE)
    hCB hBX
    hPRV hDom hFD hQNG hSVCG
    (fun M ρ rk C hz h2 => t2SeedPreShape_of C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2 (hVPr M ρ rk C hz h2))
    hVCp (fun M ρ rk C hz h2 => t2VRAK_KVRA_of
      (hVU M ρ rk C hz h2).vdom
      (hAG M ρ rk C hz h2))

end Ytosk

/-! The axioms of the new top theorem. -/
#print axioms Ytosk.trio_terminates_main_V2_curXR
