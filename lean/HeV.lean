/-
HeV.lean: 深い葉 keystone GoodChtX_deep の下流。深い葉の遠い語が FarCAt/RawWsAt を満たす
（GoodChtX_deep + OkWsAt_cons + FarCAt_of_OkWsAt）。これが topCLT_WgL_deep → GTC_far_deep →
証明中の行 BwT [K,K2] への第一歩。
-/
import HeU

namespace TRIO
namespace HeV

open Wset Small HdA HdB HdE HdH HdQ HeI HeK HeU
open GwS GxL GxP

/-- 深い葉の遠い語（子 = 深い葉 [tie 1 [tie 1 []]]、段 u、荷なし）。 -/
def dlws (u : ℕ) : List (List (List HdA.UT) × ℕ × TrioSeq) :=
  [([[HdA.UT.tie 1 [HdA.UT.tie 1 []]]], u, ([] : TrioSeq))]

/-- ★ 深い葉の遠い語は OkWsAt（子は GoodChtX_deep、荷は okRAt_nil）。 -/
theorem OkWsAt_deep {u b : ℕ} (hub : u ≤ b) : OkWsAt [] 1 b (dlws u) := by
  refine HdH.OkWsAt_cons hub ?_ (HdH.okRAt_nil [] 1 u) (HdH.OkWsAt_nil [] 1 b)
  exact HeU.GoodChtX_deep (by simp) (by simp) (by decide)

/-- ★ 深い葉の遠い語は FarCAt。 -/
theorem FarCAt_deep {u b : ℕ} (hub : u ≤ b) (b0 : ℕ) : FarCAt [] 1 (fun _ => 0) b0 (dlws u) :=
  HdH.FarCAt_of_OkWsAt (by simp) (by simp) (by decide) (dlws u) (OkWsAt_deep hub) b0

/-- ★ 深い葉の遠い語は RawWsAt。 -/
theorem RawWsAt_deep {u b : ℕ} (hub : u ≤ b) : RawWsAt [] 1 (fun _ => 0) b (dlws u) :=
  HdH.RawWsAt_of_OkWsAt (OkWsAt_deep hub)

end HeV
end TRIO
