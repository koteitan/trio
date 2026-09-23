/-
ChildLoadCOper.lean — (B) OPER hasParent-last case of childLoadC (the :133 sorry,
hasParent sub-case).  Reusable lemma for Climb to inline (like Graft61 → Graft61C).
When Y expands (hasParent trailing), the content expands in lockstep (oper_shift),
and mlift_oper' lines the copies up with Y⟦n⟧'s property (hop').
-/
import HbB
import GzD
import HdR

namespace TRIO
namespace ChildLoadCOper

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GzD GzH GzJ HbB HdR

/-- **(B) OPER hasParent-last at level u.** -/
theorem childLoadC_oper {v u : ℕ} {Y : TrioSeq}
    (hYlen2 : 2 ≤ Y.length) (hYp : hasParent Y (srow Y (Y.length - 1)) (Y.length - 1))
    (hop' : ∀ n, 1 ≤ n →
      GTC CQ u (((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 (mlift (Y⟦n⟧) v (u - v)))) :
    GTC CQ u (((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 (mlift Y v (u - v))) := by
  have hYne : Y ≠ [] := by intro h; rw [h] at hYlen2; simp at hYlen2
  set B : TrioSeq := mlift Y v (u - v) with hB
  have hBlen : B.length = Y.length := mlift_length Y v (u - v)
  have hBlen2 : 2 ≤ B.length := by rw [hBlen]; exact hYlen2
  have hBp : hasParent B (srow B (B.length - 1)) (B.length - 1) := by
    rw [hB]; exact (hasParent_mlift_iff (U := Y) v (u - v) hYne).mpr hYp
  -- content = [(1,u+1,1)] ++ shiftr01 2 0 B
  set A : TrioSeq := [((1, u + 1, 1) : ℕ × ℕ × ℕ)] with hA
  have econt : ((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 B = A ++ shiftr01 2 0 B := by
    rw [hA]; rfl
  rw [econt]
  have hAl : A.length = 1 := by rw [hA]; rfl
  have hsBlen : (shiftr01 2 0 B).length = B.length := shiftr01_length 2 0 B
  have hidx : (A ++ shiftr01 2 0 B).length - 1 = A.length + ((shiftr01 2 0 B).length - 1) := by
    rw [List.length_append, hAl, hsBlen]; omega
  have hcontlen : 2 ≤ (A ++ shiftr01 2 0 B).length := by
    rw [List.length_append, hAl, hsBlen]; omega
  have hsBp : hasParent (shiftr01 2 0 B)
      (srow (shiftr01 2 0 B) ((shiftr01 2 0 B).length - 1)) ((shiftr01 2 0 B).length - 1) := by
    rw [hsBlen, srow_shiftr01, hasParent_shiftr01]; exact hBp
  have hcontp : hasParent (A ++ shiftr01 2 0 B)
      (srow (A ++ shiftr01 2 0 B) ((A ++ shiftr01 2 0 B).length - 1))
      ((A ++ shiftr01 2 0 B).length - 1) := by
    rw [hidx, srow_append_right]
    exact hasParent_append_right_of A (shiftr01 2 0 B) hsBp
  refine GTC_oper hcontlen hcontp (fun n hn => ?_)
  rw [oper_shift A B 2 n hBlen2 hBp, hB, mlift_oper']
  have h := hop' n hn
  rw [hA]
  exact h

end ChildLoadCOper
end TRIO
