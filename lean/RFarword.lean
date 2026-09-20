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

/-- **GT_nest の語の描画**: 良い語 L の後に遠い語 `rcol 0 v W` を足した語を、段 u で
    展開したときの形。頭 (1,u+1,1)・入れ子頭 (2,u+1,1)・中身 (mlift W v (u-v))↑2。 -/
theorem rword_snoc_rcol {v : ℕ} {W : TrioSeq} (hW : Fr W) (L : List TrioSeq) {u : ℕ}
    (hu : v ≤ u) :
    rword 0 u ((L ++ [rcol 0 v W]).map (fun X => mlift X v (u - v)))
      = rword 0 u (L.map (fun X => mlift X v (u - v)))
        ++ ((1, u + 1, 1) : ℕ × ℕ × ℕ) :: ((2, u + 1, 1) : ℕ × ℕ × ℕ) ::
            shiftr01 2 0 (mlift W v (u - v)) := by
  rw [List.map_append, List.map_singleton, rword_append, rword_singleton,
    mlift_rcol hW (u - v), show v + (u - v) = u by omega, rcol_rcol]

/-! ## 二重頭のコーン -/

/-- 良い接頭辞 P の後の二重遠い語頭 (1,u+1,1)(2,u+1,1) のコーン。内側頭 (2,u+1,1) の
    行0祖先は自身と (1,u+1,1) だけで、どちらも行1 = u+1 > u。P は行0≥1 なので祖先鎖に入らない。
    oper_zcone / zcone_natDom を内側頭に適用するための条件。 -/
theorem coneV_double_head {P : TrioSeq} (hP : Fr P) (u : ℕ) :
    coneV (P ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 1) : ℕ × ℕ × ℕ)]) u (P.length + 1) := by
  rw [coneV_iff_amin,
    amin_append_right (A := P) (B := [((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 1) : ℕ × ℕ × ℕ)])
      (q := 1) (by simp) (fun x hx => by have := hP x hx; show (1 : ℕ) ≤ x.1; omega)]
  have e : ([((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 1) : ℕ × ℕ × ℕ)] : TrioSeq)
      = shiftr01 1 0 [((0, u + 1, 1) : ℕ × ℕ × ℕ), ((1, u + 1, 1) : ℕ × ℕ × ℕ)] := by
    simp [shiftr01]
  rw [e, amin_shift0]
  have h1 := amin_cons_root (S := [((1, u + 1, 1) : ℕ × ℕ × ℕ)])
    (by intro y hy; simp only [List.mem_singleton] at hy; subst hy; exact le_rfl) (u + 1) 1
    (j := 0) (by simp)
  rw [show ([((0, u + 1, 1) : ℕ × ℕ × ℕ), ((1, u + 1, 1) : ℕ × ℕ × ℕ)] : TrioSeq)
      = ((0, u + 1, 1) : ℕ × ℕ × ℕ) :: [((1, u + 1, 1) : ℕ × ℕ × ℕ)] from rfl,
    show (1 : ℕ) = 1 + 0 from rfl, h1, amin_zero]
  show u < min (u + 1) (entry [((1, u + 1, 1) : ℕ × ℕ × ℕ)] 1 0)
  rw [show entry [((1, u + 1, 1) : ℕ × ℕ × ℕ)] 1 0 = u + 1 from rfl]
  omega

/-- 良い接頭辞 P の後の二重遠い語頭を根 (0,u,0) につけた語は自然な優越域（natDom）。
    zcone_natDom を内側頭 (2,u+1,1) に適用。GT_nest 底の A1g_intro に使う。 -/
theorem natDom_double_head {P : TrioSeq} (hP : Fr P) (u : ℕ) :
    natDom (((0, u, 0) : ℕ × ℕ × ℕ) ::
      (P ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 1) : ℕ × ℕ × ℕ)])) := by
  have hP' : Fr (P ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ)]) :=
    Fr_append hP (by intro y hy; simp only [List.mem_singleton] at hy; subst hy; exact le_rfl)
  have hc : coneV ((P ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, u + 1, 1) : ℕ × ℕ × ℕ)]) u
      (P ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ)]).length := by
    rw [List.length_append, List.length_singleton, List.append_assoc,
      show ([((1, u + 1, 1) : ℕ × ℕ × ℕ)] ++ [((2, u + 1, 1) : ℕ × ℕ × ℕ)] : TrioSeq)
        = [((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 1) : ℕ × ℕ × ℕ)] from rfl]
    exact coneV_double_head hP u
  have h := zcone_natDom hP' (show 1 ≤ 2 by omega) hc
  rwa [List.append_assoc,
    show ([((1, u + 1, 1) : ℕ × ℕ × ℕ)] ++ [((2, u + 1, 1) : ℕ × ℕ × ℕ)] : TrioSeq)
      = [((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 1) : ℕ × ℕ × ℕ)] from rfl] at h

end RFarword
end TRIO
