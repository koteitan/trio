/-
RFarword.lean: 遠い語の頭を入れ子にする補題（R_farword / GT_nest）に向けた green ヘルパ群。

    GT_nest {v W} (hW : GT (v+1) W) (hWr : ∀ y ∈ W, 1 ≤ y.1) : GT v (rcol 0 v W)
    rcol 0 v W = (1, v+1, 1) :: shiftr01 1 0 W   （遠い語の頭 + 中身 W↑1）

このファイルには GT_nest の構成部品となる green な rewrite / 描画補題を積む。
-/
import GzD

namespace TRIO
namespace RFarword

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD

/-! ## 描画補題 -/

/-- 遠い語の頭を mlift すると、段が `t` 上がった遠い語の頭になる。
    mlift の cone は頭 (1,v+1,1) を通すので、頭の行1が `t` 上がる。 -/
theorem mlift_rcol {v : ℕ} {W : TrioSeq} (hW : Fr W) (t : ℕ) :
    mlift (rcol 0 v W) v t = rcol 0 (v + t) (mlift W v t) := by
  have e : rcol 0 v W = ((1, v + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 W := by
    simp [rcol]
  rw [e, mlift_letter (show v < v + 1 by omega) hW t]
  have e2 : rcol 0 (v + t) (mlift W v t)
      = ((1, v + 1 + t, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift W v t) := by
    simp only [rcol]
    refine List.cons_eq_cons.mpr ⟨?_, rfl⟩
    refine Prod.ext (by rfl) (Prod.ext ?_ (by rfl))
    show v + t + 1 = v + 1 + t; omega
  rw [e2]

/-- 遠い語の頭を二重にすると、頭 (1,u+1,1)・入れ子頭 (2,u+1,1)・中身 M↑2 になる。
    これは字を語に写す rword が rcol を 1 回、字の中身がさらに rcol を 1 回持つときの形。 -/
theorem rcol_rcol (u : ℕ) (M : TrioSeq) :
    rcol 0 u (rcol 0 u M)
      = ((1, u + 1, 1) : ℕ × ℕ × ℕ) :: ((2, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 M := by
  have e : rcol 0 u M = ((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 M := by simp [rcol]
  rw [e]
  show ((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 M)
      = _
  rw [show shiftr01 1 0 (((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 M)
      = ((2, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (shiftr01 1 0 M) by simp [shiftr01]]
  rw [shiftr01_add0]

end RFarword
end TRIO
