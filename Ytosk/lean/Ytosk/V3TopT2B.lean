/-
**最上位の定理で T2BelowXRes を小さい残りに替える（2026-10-17、t2）。**

`trio_terminates_main_V2_cur`（V3TopV2）の仮定 `T2BelowXResV2` を `t2BelowXResV2_of`（V3T2BelowV2）で埋める。
新しい残りは種での RClaimU・REr と AbsWN（`T2BelowRV2`）と種の閉じた形の標準形（`T2SeedOTV2`）。
RwClosed M は既にある t0 の残り `T0RwRes`、種の残りは既にある `T2SeedPResRCV2`・`HSibHardV2` から。
-/
import Ytosk.V3TopV2
import Ytosk.V3T2BelowV2
import Ytosk.V3T2BelowR
import Ytosk.V3T2SeedPre
import Ytosk.V3T2SeedOTP

namespace Ytosk

/-- **The top theorem with `T2BelowXRes` split**: the residual before `x` is `T2BelowRV2` and `T2SeedOTV2`. -/
theorem trio_terminates_main_V2_t2B (hD : HDropV2) (hSd : HSeedV2)
    (hF : HFrameV2) (hLf : HLeafV2)
    (hRw : T0RwRes) (hAbW : T0AbWRes)
    (hBR : T2BelowRV2) (hOT : T2SeedOTV2) (hPR : T2SeedPResRCV2) (hSib : HSibHardV2) (hDom : T2SeedDomV2)
    (hFD : FDsh)
    (hQNG : ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r →
        par M 0 (r + L) = some q → q ≠ r → ∀ Lc, CL M r = Lc ++ [q] → T2VRAQNDom M ρ r L q Lc)
    (hSVCG : ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRASeedSVC M)
    (hVPr : ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2SeedPreShape M ρ)
    (hVCp : ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRACopy M)
    (hVK : ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRAK KStepVRA M) : WellFounded Step' :=
  trio_terminates_main_V2_cur hD hSd hF hLf hRw hAbW
    (t2BelowXResV2_of hRw hBR (t2SeedPResV2_of (t2SeedPResR_of_sib (hSib_of_hard hSib) hPR)) hOT)
    hPR hSib hDom hFD hQNG hSVCG hVPr hVCp hVK

/-- **The top theorem with the part before `x` in `M`-only residuals**: `T2BelowRV2` is replaced by the
closedness of the seed argument `T2SeedClV2` (qn・sv・C) and the bump monotonicity `T2BumpMonoV2`; the
prefix shape of the seed frames `T2SeedPreShape` only in the sv・C cases (`T2SeedPreShapeSVC`), and the
seed standard forms only for qn・sv・C (`T2SeedOTRestV2`). -/
theorem trio_terminates_main_V2_t2C (hD : HDropV2) (hSd : HSeedV2)
    (hF : HFrameV2) (hLf : HLeafV2)
    (hRw : T0RwRes) (hAbW : T0AbWRes)
    (hCl : T2SeedClV2) (hBM : T2BumpMonoV2) (hOT : T2SeedOTRestV2) (hPR : T2SeedPResRCV2) (hSib : HSibHardV2)
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
  trio_terminates_main_V2_t2B hD hSd hF hLf hRw hAbW
    (t2BelowRV2_of (t2SeedPResV2_of (t2SeedPResR_of_sib (hSib_of_hard hSib) hPR)) hCl hBM)
    (t2SeedOTV2_of (t2SeedPResV2_of (t2SeedPResR_of_sib (hSib_of_hard hSib) hPR)) hOT)
    hPR hSib hDom hFD hQNG hSVCG
    (fun M ρ rk C hz h2 => t2SeedPreShape_of C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ hz h2 (hVPr M ρ rk C hz h2))
    hVCp hVK

end Ytosk
