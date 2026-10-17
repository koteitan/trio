/-
**今の最上位の定理（2026-10-17、t2・top）。**

`trio_terminates_main_V2_base`（V3TopV2）の仮定 `T2BelowXResV2` を `t2BelowXResV2_of`（V3T2BelowV2）で埋め、
x より前の残り `T2BelowRV2` を `t2BelowRV2_of`（V3T2BelowR）で、種の標準形 `T2SeedOTV2` を `t2SeedOTV2_of`
（V3T2SeedOTP）で、種の列の枠の形 `T2SeedPreShape` を `t2SeedPreShape_of`（V3T2SeedPre）で小さい残りに替える。
文脈の弱い閉じ方 RwClosedL は残り HRwClL から（RwClosed は標準形で偽、V3ShadowL）。種の残りは `T2SeedPResRCV2` と、兄弟の値の条件 `HSibColV2`（V3SibCol の SibColW）から。
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

namespace Ytosk

/-- **The sibling value condition `SibColU` of every standard matrix** (replaces `HSibHardV2`; two counted
children are covered by `Good3.dec`, two bump children by `v_bump_sib`). -/
def HSibColV2 : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Rk N rk → Good3 N σ → SibColU N σ

theorem hSibHard_of_col (h : HSibColV2) : HSibHardV2 := fun N σ rk hN hS hC hR hG =>
  upgSibVHard_of_col (sInvXJ_std hN hS).1 (sInvXJ_std hN hS).2 hC hR hG
    (sibColW_of_U (sInvXJ_std hN hS).1 hC hG (h N σ rk hN hS hC hR hG))

/-- **The current top theorem.** The hypotheses are the named residuals:
drop `HDropV2W`・`HSeedV2`, the strong absorption at `t = 0` `T0UpgAbsV2` (t0); shared `HFrameV2`・`HLeafV2`; t0 `T0ArgBRes`; the bump monotonicity along prefixes `HBumpExt` (gives t0's `T0AbWRes` and t2's `T2BumpMonoV2`); the weak closedness `HRwClL` of every standard matrix (gives `T0RwRes` and the shadow frames of t0・t2); `T2VAncStep` (with `T2VRAK KAG` the frame condition `KVRA`);
t2 the closedness of the seed argument `T2SeedClV2B` (qn, and the `k`-free sv・C parts `T2SeedSVBase`・`T2SeedCBase`),
the strong `UpgAbsX` at the last column `T2UpgAbsW` (drop-wkx2), (the seed standard forms come from `T2SeedClV2B`), the seed residual `T2SeedPResRCV2B` (qn and C reduced), `T2SeedDomV2`, `FDsh`,
the seed columns (qn from `T2SeedDomV2` and `T2SeedQNBase`; sv `T2SVc0`, C `T2CFrRes`), the prefix shape of the seed frames (from `T2SVc0`・`T2CFrRes`), the copy levels `T2VRACopy`; t1 the `σ`-step at the guarded copy frames
`T2VRAK KAG` (with `T2VAncStep` it gives the frame condition `KVRA` of `qVRAshK_KVRA`); top `HSibColV2` (adjacent siblings with the same column, not both counted, `SibColU`). -/
theorem trio_terminates_main_V2_cur (hDW : HDropV2W) (hU0 : T0UpgAbsV2) (hSd : HSeedV2)
    (hF : HFrameV2) (hLf : HLeafV2)
    (hBE : HBumpExt) (hArgB : T0ArgBRes) (hCB : T2CBadOut) (hRL : HRwClL)
    (hVS : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VAncStep M)
    (hCl : T2SeedClV2B) (hU2 : T2UpgAbsW) (hPRB : T2SeedPResRCV2B) (hSC : HSibColV2)
    (hDom : T2SeedDomV2) (hFD : FDsh)
    (hSV0 : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
        T2SVCase M r L → T2SVc0 M ρ r L)
    (hCF : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r →
        par M 0 (r + L) = some q → q ≠ r → (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2CFrRes M ρ r L q)
    (hVCp : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRACopy M)
    (hAG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRAK KAG M) : WellFounded Step' :=
  have hSib : HSibHardV2 := hSibHard_of_col hSC
  have hQNG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r →
        par M 0 (r + L) = some q → q ≠ r → ∀ Lc, CL M r = Lc ++ [q] → T2VRAQNDom M ρ r L q Lc :=
    fun M ρ rk C hz h2 r L q hlen hr hq hqr Lc hCL =>
      t2VRAQNDom_of ((hDom M ρ rk C hz h2).1 r L q hlen hr hq hqr Lc hCL)
        (fun hL => by
          subst hL
          exact t2VRAQNDom0_of (Inv3W.ofV2 C.S C.I) hlen
            ((hCl M ρ rk C hz h2 r L hlen hr).1 q [] hq hqr hCL)
            (fun τ hτ => let ⟨t1, he, _⟩ := (hPRB M ρ rk C hz h2).qn r L q hlen hr hq hqr [] hCL τ hτ; ⟨t1, he⟩))
  have hPR : T2SeedPResRCV2 := t2SeedPResRCV2_of_B hCl hPRB
  have hP : T2SeedPResV2 := t2SeedPResV2_of (t2SeedPResR_of_sib (hSib_of_hard hSib) hPR)
  have hBX : T2BelowXResV2 := t2BelowXResV2_of t0RwRes_ctx (t2BelowRV2_of hP (t2SeedClV2_of_B hCl) (t2BumpMonoV2_of_ext hBE)) hP (t2SeedOTV2_of hP (t2SeedOTRestV2_of_B hCl))
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
  trio_terminates_main_V2_base (hDropV2_of hDW hU0) hSd hF hLf
    (t0AbWRes_of_ext (hDropV2_of hDW hU0) hBE) hArgB
    hRL hCB hBX hU2
    hPR hSib hDom hFD hQNG hSVCG
    (fun M ρ rk C hz h2 => t2SeedPreShape_of C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ hz h2 (hVPr M ρ rk C hz h2))
    hVCp (fun M ρ rk C hz h2 => t2VRAK_KVRA_of
      (t2CopyK_vDom_of (hBX M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ hz h2 (hVS M ρ rk C hz h2))
      (hAG M ρ rk C hz h2))

end Ytosk
