import HbB
import GzD
import HdR

namespace TRIO
namespace ConeOrph

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GzD GzH GzJ HbB HdR

/-- ¬hasParent(row1) の孤児 (row1=v+1) は coneV。noParent_of_coneV の converse。 -/
theorem coneV_of_orph {Y : TrioSeq} {v : ℕ} (hYne : Y ≠ [])
    (hY1 : entry Y 1 (Y.length - 1) = v + 1)
    (hYorph : ¬ hasParent Y 1 (Y.length - 1)) :
    coneV Y v (Y.length - 1) := by
  have hYl : 0 < Y.length := List.length_pos_iff.mpr hYne
  intro y hy
  by_contra hle
  rw [not_lt] at hle
  have hlt : entry Y 1 y < entry Y 1 (Y.length - 1) := by rw [hY1]; omega
  exact hYorph (H12Export.hasParent1_of_le0_witness (by omega) hy hlt)

end ConeOrph
end TRIO
