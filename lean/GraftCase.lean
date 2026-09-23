/-
GraftCase.lean — the GRAFT j≤v case of childLoad (GT_nest / psiI keystone).

childLoad's GRAFT content = (1,v+1,1) :: shiftr01 2 0 Y with Y's trailing an orphan
(row1=j∈[1,v], row2=0).  Decompose content = K ++ [(h_y+2, j, 0)],
K = (1,v+1,1) :: shiftr01 2 0 Y.dropLast, tie = shifted Y-trailing.  Apply GTC_orph:
  hnp  = row1_noCross (via noParent_ctx, rsum-free),
  hzK  = childLoad's own graft datum hgr, via the graft/shift commutation
         (1,v+1,1)::shiftr01 2 0 (graft Y z) = K ++ shiftr01 (h_y+2) 0 z.
-/
import HbB
import GzD

namespace TRIO
namespace GraftCase

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GzD GzJ HbB

/-- row1-noCross (rsum-free hnp), inlined from Row1NoCross. -/
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

/-- **GRAFT j≤v case (GREEN target):** the content GTC from Y's graft datum. -/
theorem childLoad_graft {v j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ v) {Y : TrioSeq} (hYne : Y ≠ [])
    (hYj : entry Y 1 (Y.length - 1) = j) (hY2 : entry Y 2 (Y.length - 1) = 0)
    (hYorph : ¬ hasParent Y 1 (Y.length - 1))
    (hzK : ∀ z ∈ Wg (2 * j - 1), based z →
      GTC CQ v (((1, v + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 (graft Y z))) :
    GTC CQ v (((1, v + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 Y) := by
  have hYlen : 0 < Y.length := List.length_pos_iff.mpr hYne
  set h_y : ℕ := entry Y 0 (Y.length - 1) with hhy
  -- Y = Y.dropLast ++ [trailing];  trailing = (h_y, j, 0)
  have hg : Y.getLast hYne = ((h_y, j, 0) : ℕ × ℕ × ℕ) := by
    have h1 : Y.getD (Y.length - 1) (0, 0, 0) = Y.getLast hYne := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
        List.getLast_eq_getElem]
      rfl
    rw [← h1, getD_eq_entries, ← hhy, hYj, hY2]
  have htrail : Y = Y.dropLast ++ [((h_y, j, 0) : ℕ × ℕ × ℕ)] := by
    rw [← hg]; exact (List.dropLast_append_getLast hYne).symm
  -- content = K ++ [(h_y+2, j, 0)],  K = (1,v+1,1) :: shiftr01 2 0 Y.dropLast
  set K : TrioSeq := ((1, v + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 Y.dropLast with hKdef
  have hcontent : ((1, v + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 Y
      = K ++ [((h_y + 2, j, 0) : ℕ × ℕ × ℕ)] := by
    rw [hKdef]
    conv_lhs => rw [htrail]
    rw [shiftr01_append0]
    simp only [shiftr01, List.map_cons, List.map_nil, List.cons_append, Nat.add_zero]
  rw [hcontent]
  refine GTC_orph (C := CQ) (v := v) (K := K) (h := h_y + 2) (j := j) hj1 hj ?_ ?_
  · -- hnp = row1-noCross
    have h := row1_noCross_content (v := v) (j := j) hj hYne hYj hYorph
    rw [hcontent] at h
    exact h
  · -- hzK from graft datum + commutation
    intro z hz hbz
    have hg := hzK z hz hbz
    -- (1,v+1,1)::shiftr01 2 0 (graft Y z) = K ++ shiftr01 (h_y+2) 0 z
    have ecomm : ((1, v + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 (graft Y z)
        = K ++ shiftr01 (h_y + 2) 0 z := by
      rw [hKdef, List.cons_append]
      congr 1
      unfold graft
      rw [← hhy, shiftr01_append0]
      congr 1
      simp only [shiftr01, List.map_map]
      apply List.map_congr_left
      intro p _
      simp only [Function.comp_apply, Prod.mk.injEq, and_true]
      omega
    rw [ecomm] at hg
    exact hg

end GraftCase
end TRIO
