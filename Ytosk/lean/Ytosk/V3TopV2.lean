/-
**t = 2 の生産者を差し込んだ現状の最上位（2026-10-16、top）。**

- `trio_terminates_main_V2_t2`: `trio_terminates_main_V2_glob` の `ExpT2V2`・`R2V2` を t2 の
  `expT2V2_of`・`r2V2_of`（V3ExpT2V2）で埋めたもの。枠と葉は共通の残り `HFrameV2`・`HLeafV2`。
- `T2SeedPResRV2`・`t2SeedPResV2_of`: 種の残り `T2SeedPResV2` を、t2 が M だけで決まる欄を外した
  `T2SeedPResR`（V3T2SeedRes）に替える。
- `trio_terminates_main_V2_t2R`: 上の最上位で種の残りを `T2SeedPResRV2` に替えたもの。
-/
import Ytosk.V3ExpT2V2
import Ytosk.V3T2SeedRes

namespace Ytosk

open T

/-- **The current top theorem with the `t = 2` producers plugged in.** -/
theorem trio_terminates_main_V2_t2 (hD : HDropV2) (hSd : HSeedV2) (hA : HAbSV2)
    (hF : HFrameV2) (hLf : HLeafV2)
    (hCut : T0CutResGGC)
    (h1 : ExpT1V2)
    (hB : T2BelowXRes) (hFO : T2FOSeedV2) (hPR : T2SeedPResV2) (hVF : T2VSFCV2) (hVA : T2VRAV2) :
    WellFounded Step' :=
  trio_terminates_main_V2_glob hD hSd hA hF hLf hCut h1
    (expT2V2_of hB hFO hPR hVF hVA hF hLf) (r2V2_of hB)

/-- **t2-seed, reduced**: the seed residual with the fields fixed by `M` alone removed (V3T2SeedRes). -/
def T2SeedPResRV2 : Prop :=
  ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    T2SeedPResR M ρ

theorem t2SeedPResV2_of (h : T2SeedPResRV2) : T2SeedPResV2 := by
  intro M ρ rk C hz h2
  exact t2SeedPRes_of C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ (h M ρ rk C hz h2)

/-- **The current top theorem with the reduced seed residual.** -/
theorem trio_terminates_main_V2_t2R (hD : HDropV2) (hSd : HSeedV2) (hA : HAbSV2)
    (hF : HFrameV2) (hLf : HLeafV2)
    (hCut : T0CutResGGC)
    (h1 : ExpT1V2)
    (hB : T2BelowXRes) (hFO : T2FOSeedV2) (hPR : T2SeedPResRV2) (hVF : T2VSFCV2) (hVA : T2VRAV2) :
    WellFounded Step' :=
  trio_terminates_main_V2_t2 hD hSd hA hF hLf hCut h1 hB hFO (t2SeedPResV2_of hPR) hVF hVA

end Ytosk
