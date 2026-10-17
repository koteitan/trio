/-
**今の最上位の定理（2026-10-17、t2・top）。**

`trio_terminates_main_V2_base`（V3TopV2）の仮定 `T2BelowXResV2` を `t2BelowXResV2_of`（V3T2BelowV2）で埋め、
x より前の残り `T2BelowRV2` を `t2BelowRV2_of`（V3T2BelowR）で、種の標準形 `T2SeedOTV2` を `t2SeedOTV2_of`
（V3T2SeedOTP）で、種の列の枠の形 `T2SeedPreShape` を `t2SeedPreShape_of`（V3T2SeedPre）で小さい残りに替える。
RwClosed M は既にある t0 の残り `T0RwRes`、種の残りは既にある `T2SeedPResRCV2`・`HSibHardV2` から。
最上位はこのファイルの `trio_terminates_main_V2_cur` 1 本。
-/
import Ytosk.V3TopV2
import Ytosk.V3T2BelowV2
import Ytosk.V3T2BelowR
import Ytosk.V3T2SeedPre
import Ytosk.V3T2SeedOTP
import Ytosk.V3RwCarry

namespace Ytosk

/-- **The current top theorem.** The hypotheses are the named residuals:
drop `HDropV2W`・`HSeedV2`, the strong absorption at `t = 0` `T0UpgAbsV2` (t0); shared `HFrameV2`・`HLeafV2`; t0 `T0AbWRes`・`T0ArgBRes`; `RwClosed` of the `t = 2` expansions from `T2X1Cl`・`T2CopyK CopyLowK`・`T2VAncStep` (`RwClosed` is carried by the induction, so `T0RwRes` holds);
t2 the closedness of the seed argument `T2SeedClV2` (qn・sv・C), the bump monotonicity `T2BumpMonoV2`,
the strong `UpgAbsX` at the last column `T2UpgAbsW` (drop-wkx2), the seed standard forms for qn・C `T2SeedOTRestV2`, the seed residual `T2SeedPResRCV2`, `T2SeedDomV2`, `FDsh`,
the seed columns (`T2VRAQNDom`・`T2VRASeedSVC`), the prefix shape of the seed frames for sv・C
(`T2SeedPreShapeSVC`), the copy levels `T2VRACopy`; t1 the `σ`-step at the guarded copy frames
`T2VRAK KStepVRA`; top `HSibHardV2`. -/
theorem trio_terminates_main_V2_cur (hDW : HDropV2W) (hU0 : T0UpgAbsV2) (hSd : HSeedV2)
    (hF : HFrameV2) (hLf : HLeafV2)
    (hAbW : T0AbWRes) (hArgB : T0ArgBRes)
    (hX1 : ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → G.T2X1Cl M ρ)
    (hLow : ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2CopyK CopyLowK M)
    (hVS : ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VAncStep M)
    (hCl : T2SeedClV2) (hBM : T2BumpMonoV2) (hU2 : T2UpgAbsW) (hOT : T2SeedOTRestV2) (hPR : T2SeedPResRCV2) (hSib : HSibHardV2)
    (hDom : T2SeedDomV2) (hFD : FDsh)
    (hQNG : ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r →
        par M 0 (r + L) = some q → q ≠ r → ∀ Lc, CL M r = Lc ++ [q] → T2VRAQNDom M ρ r L q Lc)
    (hSVCG : ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRASeedSVC M)
    (hVPr : ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2SeedPreShapeSVC M ρ)
    (hVCp : ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRACopy M)
    (hVK : ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRAK KStepVRA M) : WellFounded Step' :=
  have hP : T2SeedPResV2 := t2SeedPResV2_of (t2SeedPResR_of_sib (hSib_of_hard hSib) hPR)
  have hBX : T2BelowXResV2 := t2BelowXResV2_of t0RwRes_ctx (t2BelowRV2_of hP hCl hBM) hP (t2SeedOTV2_of hP hOT)
  trio_terminates_main_V2_base (hDropV2_of hDW hU0) hSd hF hLf hAbW hArgB
    (tRwOut2_of hBX hP hX1 hLow hVS) hBX hU2
    hPR hSib hDom hFD hQNG hSVCG
    (fun M ρ rk C hz h2 => t2SeedPreShape_of C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ hz h2 (hVPr M ρ rk C hz h2))
    hVCp hVK

end Ytosk
