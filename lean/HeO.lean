/-
HeO.lean: 生成器のための形（最上段の段つきの木の並びの条件の組み立て）。
-/
import HeN

namespace TRIO
namespace HeO

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open HdA HeK

theorem TreeTss_nil (v : ℕ) : ∀ us ∈ ([] : List (List UT)), TreeTs v 0 true us := fun _ h => by simp at h

theorem TreeTss_cons {v : ℕ} {us : List UT} {Uss : List (List UT)} (h1 : TreeTs v 0 true us)
    (h2 : ∀ us' ∈ Uss, TreeTs v 0 true us') : ∀ us' ∈ us :: Uss, TreeTs v 0 true us' := by
  intro us' h
  rcases List.mem_cons.mp h with rfl | h
  · exact h1
  · exact h2 us' h

end HeO
end TRIO
