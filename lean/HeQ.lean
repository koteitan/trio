/-
HeQ.lean: 深い葉の flat core（葉が深い位置にある上の葉の展開。悪い根 = 段の低い祖先）。

- upleaf_deep_core: 塊 (1,q,0) :: R↑1（R の最後の列が葉、srow = 1、根 (0,q,0) が葉の段 1 の親）は、
  展開 tow q 0 R m'（葉の row0 の深さで graft、oper_cons_tower1）が全て GpT なら GpT。
  HeH.upleaf_core を、葉が深い位置（R が入れ子の descent）でも使えるように一般化した（towR への変換をしない）。
- Xtow / chT_Xtow: 深い葉の塔の木（葉の位置に tie0 の複製を入れ子）の像 = 葉なしの descent ++ 深さ Q.length+1 の tow。
-/
import HeH

namespace TRIO
namespace HeQ

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HaG HbD HbM HbP HbS HcA HcE HcF HcI HcM HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ
open HeB HeC HeD HeE HeF HeG HeH

/-! ## 深い葉の木の塔 -/

/-- 深い葉の塔の木: 葉の位置に「段 0 の節点（= 悪い根 F の複製）が道 Q を下る」を入れ子にする。 -/
def Xtow (Q : Path) (us : List UT) : ℕ → List UT
  | 0 => us
  | j + 1 => us ++ [UT.tie 0 (plugQ Q (Xtow Q us j))]

theorem chT_plugQ_snoc (b r u : ℕ) (Q : Path) (us : List UT) (x : UT) :
    chT b r u (plugQ Q (us ++ [x]))
      = chT b r u (plugQ Q us) ++ shiftr01 Q.length 0 (unitT b r u x) := by
  rw [chT_plugQ, chT_snoc, shiftr01_append0, ← List.append_assoc, ← chT_plugQ]

/-- ★ 深い葉の塔の木の像 = 葉なしの descent ++ 葉の深さ Q.length+1 の graft の塔（tow）。 -/
theorem chT_Xtow (b r u : ℕ) (Q : Path) (us : List UT) (l : ℕ) :
    ∀ j, chT b r u (plugQ Q (Xtow Q us j))
      = chT b r u (plugQ Q us) ++ shiftr01 (Q.length + 1) 0
          (tow r 0 (chT b r u (plugQ Q (us ++ [UT.tie l []]))) j) := by
  obtain ⟨R, hRdef⟩ : ∃ R, R = chT b r u (plugQ Q (us ++ [UT.tie l []])) := ⟨_, rfl⟩
  have hRsnoc : R = chT b r u (plugQ Q us) ++ [((Q.length + 1, r + l, 0) : ℕ × ℕ × ℕ)] := by
    rw [hRdef, chT_plugQ_snoc]
    congr 1
    simp only [unitT, chT, shiftr01, List.map_cons, List.map_nil]
    congr 1
    refine Prod.ext ?_ (Prod.ext rfl rfl)
    simp [Nat.add_comm]
  have hRdl : R.dropLast = chT b r u (plugQ Q us) := by rw [hRsnoc, List.dropLast_concat]
  have hRlast : entry R 0 (R.length - 1) = Q.length + 1 := by
    rw [hRsnoc,
      show (chT b r u (plugQ Q us) ++ [((Q.length + 1, r + l, 0) : ℕ × ℕ × ℕ)]).length - 1
        = (chT b r u (plugQ Q us)).length from by simp,
      show (chT b r u (plugQ Q us)).length = (chT b r u (plugQ Q us)).length + 0 from rfl,
      entry_append_right]
    rfl
  rw [← hRdef]
  intro j
  induction j with
  | zero => simp [Xtow, tow, shiftr01]
  | succ j ih =>
      rw [Xtow, chT_plugQ_snoc]
      have eU : unitT b r u (UT.tie 0 (plugQ Q (Xtow Q us j)))
          = ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT b r u (plugQ Q (Xtow Q us j))) := by
        simp only [unitT, Nat.add_zero]
      rw [eU, ih, tow, graft_eq_shift, hRlast, hRdl]
      obtain ⟨Z, hZ⟩ : ∃ Z, Z = chT b r u (plugQ Q us) ++ shiftr01 (Q.length + 1) 0 (tow r 0 R j) :=
        ⟨_, rfl⟩
      rw [← hZ]
      congr 1
      rw [show ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Z = [((1, r, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 1 0 Z
          from rfl,
        show ((0, r, 0) : ℕ × ℕ × ℕ) :: Z = [((0, r, 0) : ℕ × ℕ × ℕ)] ++ Z from rfl,
        shiftr01_append0, shiftr01_append0, shiftr01_add0, Nat.add_comm 1 Q.length]
      congr 1
      simp only [shiftr01, List.map_cons, List.map_nil]
      congr 1
      refine Prod.ext ?_ (Prod.ext rfl rfl)
      simp; omega

/-! ## flat core -/

section
variable {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o) (f : ℕ → ℕ)
include hA hA1 ho

/-- ★ 深い葉の展開（葉の深さ d0 で graft する塔）。R の最後の列が葉。 -/
theorem upleaf_deep_core {b d q : ℕ} {Pre Yp R : TrioSeq}
    (hPre : Fr Pre) (hYp : Fr Yp) (hYpH : Hd Yp) (hYpne : Yp ≠ [])
    (hRok : argOK R) (hRne : R ≠ [])
    (hd_ : domT R (entry R 1 (R.length - 1)))
    (hsr : srow R (R.length - 1) = 1)
    (hpM : hasParent (((0, q, 0) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length)
    (hrep : ∀ m', 1 ≤ m' → GpT A o f b
      (Pre ++ (Yp ++ shiftr01 d 0 (shiftr01 1 0 (tow q 0 R m'))))) :
    GpT A o f b (Pre ++ (Yp ++ shiftr01 d 0 (shiftr01 1 0 (((0, q, 0) : ℕ × ℕ × ℕ) :: R)))) := by
  have hRl : 0 < R.length := List.length_pos_iff.mpr hRne
  have hlen2 : 2 ≤ (((0, q, 0) : ℕ × ℕ × ℕ) :: R).length := by simp; omega
  have hpM' : hasParent (((0, q, 0) : ℕ × ℕ × ℕ) :: R)
      (srow (((0, q, 0) : ℕ × ℕ × ℕ) :: R) ((((0, q, 0) : ℕ × ℕ × ℕ) :: R).length - 1))
      ((((0, q, 0) : ℕ × ℕ × ℕ) :: R).length - 1) := by
    have hl : ((((0, q, 0) : ℕ × ℕ × ℕ) :: R).length - 1) = R.length := by simp
    rw [hl, srow_cons_last hRne]; exact hpM
  refine tstep_oper hA hA1 ho f hPre hYp hYpH hYpne (Fr_shift1 _)
    (by rw [shiftr01_length]; exact hlen2)
    (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpM') (fun m' hm' => ?_)
  have eO := oper_shift [] (((0, q, 0) : ℕ × ℕ × ℕ) :: R) 1 m' hlen2 hpM'
  simp only [List.nil_append] at eO
  rw [eO, oper_cons_tower1 hRok hRne hd_ hsr hpM]
  exact hrep m' hm'

end

end HeQ
end TRIO
