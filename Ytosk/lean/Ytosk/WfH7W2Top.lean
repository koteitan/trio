/-
**最上位への差し込みの確認（2026-10-31, WfH7W2）。** `trio_terminates_main_V2_cur` の残り hB2 : HUACB2・
hSib : H7WSib を、`B2Step`（Bad2 の下の StepDom）と構造の残り `SibMCol`（Bad2 なし・値なし）に置き換える。
-/
import Ytosk.V3TopT2B
import Ytosk.WfH7W2Ret
import Ytosk.WfH7W2Sib

namespace Ytosk.WfH7W2

open T

theorem trio_terminates_main_V2_h7w2 (hDU : HDropU) (hTB2 : T2BadRes) (hStep : B2Step) (hSibC : SibMCol)
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
  trio_terminates_main_V2_cur hDU hTB2 (huacB2_of_step hStep) (h7wSib_of_col hSibC) hF hLf hBE hCB hVU hClR hPRE
    hCan hDomQ hVCp hAG

#print axioms trio_terminates_main_V2_h7w2

end Ytosk.WfH7W2
