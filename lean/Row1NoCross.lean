/-
Row1NoCross.lean — the GRAFT j≤v atomic gap of childLoad (GT_nest / psiI keystone).

childLoad's GRAFT content is  (1,v+1,1) :: shiftr01 2 0 Y  with Y's trailing an
orphan (row1 = j ≤ v, row2 = 0, from domT Y (2j-1)).  To use the graft clause we
need  hnp : ¬ hasParent content 1 (last)  WITHOUT rsum.  `noParent_ctx` (GxN:399)
with A = [head], B = shiftr01 2 0 Y makes the non-crossing `hpre` trivial (only the
head, row1 = v+1 ≥ j) and `hnp` on B comes from Y's orphan via `hasParent_shiftr01`.
-/
import GxN
import GzD

namespace TRIO
namespace Row1NoCross

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GzD

/-- **row1-noCross (GREEN):** the far-word head + shifted orphan content `Y` has no
row-1 parent at its trailing.  Discharges GTC_orph's `hnp` for the GRAFT j≤v case,
rsum-free. -/
theorem row1_noCross_content {v j : ℕ} (hj : j ≤ v) {Y : TrioSeq} (hYne : Y ≠ [])
    (hj_eq : entry Y 1 (Y.length - 1) = j)
    (hYorph : ¬ hasParent Y 1 (Y.length - 1)) :
    ¬ hasParent (((1, v + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 Y) 1
      ((((1, v + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 Y).length - 1) := by
  have hYlen : 0 < Y.length := List.length_pos_iff.mpr hYne
  set A : TrioSeq := [((1, v + 1, 1) : ℕ × ℕ × ℕ)] with hA
  set B : TrioSeq := shiftr01 2 0 Y with hB
  have hBlen : B.length = Y.length := by rw [hB]; exact shiftr01_length 2 0 Y
  have econt : ((1, v + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 Y = A ++ B := by rw [hA, hB]; rfl
  rw [econt]
  have hAl : A.length = 1 := by rw [hA]; rfl
  have hidx : (A ++ B).length - 1 = A.length + (Y.length - 1) := by
    rw [List.length_append, hBlen, hAl]; omega
  rw [hidx]
  refine noParent_ctx (A := A) (B := B) (b := Y.length - 1) (j := j) ?_ ?_ ?_ ?_
  · rw [hBlen]; omega
  · intro k hk _
    have hk0 : k = 0 := by rw [hA] at hk; simp at hk; omega
    subst hk0
    show j ≤ entry A 1 0
    rw [hA]; show j ≤ v + 1; omega
  · rw [hB, entry1_shiftr01, hj_eq]
  · rw [hB, hasParent_shiftr01]; exact hYorph

end Row1NoCross
end TRIO
