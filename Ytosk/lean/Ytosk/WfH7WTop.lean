/-
**トップの差し替えの型の確認（2026-10-31, WfH7W）。** V3TopT2B は編集しない。`hH7W` と `T2BadRes` の第 2 欄
`T2QNDomBad` を `HUACB2`・`H7WSib`・`T2QNDomBad2` に替えた形が、そのまま `trio_terminates_main_V2_cur` に入る。
-/
import Ytosk.V3TopT2B
import Ytosk.WfH7WSib

namespace Ytosk.WfH7W

open T

theorem trio_terminates_main_V2_h7w (hDU : HDropU) (hSrc : WfT2Src.T2AbsNSrcW) (hQB2 : T2QNDomBad2)
    (hB2 : HUACB2) (hSib : H7WSib)
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
  trio_terminates_main_V2_cur hDU ⟨hSrc, t2QNDomBad_of_B2 hB2 hQB2⟩ (t0BadSeedsH7W_of_sib hDU hB2 hSib)
    hF hLf hBE hCB hVU hClR hPRE hCan hDomQ hVCp hAG

end Ytosk.WfH7W
