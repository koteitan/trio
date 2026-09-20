import GxN
import GzD

namespace TRIO
namespace Gtrc4test

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GzD

def Trc4 : TrioSeq := [((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ)]

theorem mono01 : ∀ a b, Relation.ReflTransGen (nextrel0 Trc4) a b → a ≤ b := by
  intro a b h
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans ih (le_of_lt (nextrel0_lt hbc))

/-- shiftr01 の行0シフトの合成。 -/
theorem shiftr01_comp (a b : ℕ) (X : TrioSeq) :
    shiftr01 a 0 (shiftr01 b 0 X) = shiftr01 (a + b) 0 X := by
  simp only [shiftr01, List.map_map]
  apply List.map_congr_left
  intro c _
  simp only [Function.comp_apply]
  exact Prod.ext (by dsimp only; omega) rfl

/-- **KEYSTONE(frontier)**: 遠い語(far-word)を content として入れ子にする。
    深さ v+1 で良い content W を rcol で包むと深さ v で良い content になる。
    = 「字の中身の中の字」の閉包。既存機構に無い新規補題。 -/
theorem GT_nest {v : ℕ} {W : TrioSeq} (hW : GT (v + 1) W) (hWr : ∀ y ∈ W, 1 ≤ y.1) :
    GT v (rcol 0 v W) := by
  sorry

theorem gt_trc4 : GT 0 Trc4 := by
  have e : Trc4 = ([((1, 1, 1) : ℕ × ℕ × ℕ)] : TrioSeq) ++ [((2, 1, 0) : ℕ × ℕ × ℕ)] := rfl
  rw [e]
  refine GT_tie (v := 0) (K := [((1, 1, 1) : ℕ × ℕ × ℕ)]) (x := 2) ?_ ?_
  · -- hcone : coneV Trc4 0 1
    intro y hy
    have hyle : y ≤ 1 := mono01 y 1 hy
    show 0 < entry ([((1,1,1):ℕ×ℕ×ℕ)] ++ [((2,1,0):ℕ×ℕ×ℕ)]) 1 y
    obtain rfl | rfl : y = 0 ∨ y = 1 := by omega
    · decide
    · decide
  · -- hload : ∀u≥0, ∀Z∈Wg(2u) based, GT u ([(1,u+1,1)] ++ shiftr01 2 0 Z)
    intro u _ Z hZ hb
    -- mlift [(1,1,1)] 0 (u-0) = [(1,u+1,1)]
    have hmlift : mlift ([((1, 1, 1) : ℕ × ℕ × ℕ)] : TrioSeq) 0 (u - 0)
        = [((1, u + 1, 1) : ℕ × ℕ × ℕ)] := by
      rw [Nat.sub_zero]
      have h : mlift ([((1, 0 + 1, 1) : ℕ × ℕ × ℕ)] : TrioSeq) 0 u
          = [((1, 0 + 1 + u, 1) : ℕ × ℕ × ℕ)] := mlift_one_letter 0 u
      rw [show (0 : ℕ) + 1 = 1 from rfl] at h
      rw [h, Nat.add_comm 1 u]
    rw [hmlift]
    -- [(1,u+1,1)] ++ shiftr01 2 0 Z = rcol 0 u (shiftr01 1 0 Z)
    have hrw : ([((1, u + 1, 1) : ℕ × ℕ × ℕ)] : TrioSeq) ++ shiftr01 2 0 Z
        = rcol 0 u (shiftr01 1 0 Z) := by
      rw [rcol, show (0 : ℕ) + 1 = 1 from rfl, shiftr01_comp 1 1 Z,
        show (1 : ℕ) + 1 = 2 from rfl]
      rfl
    rw [hrw]
    -- GT_nest applied to W = shiftr01 1 0 Z, good at level u+1 via GT_loadTop
    have hWgt : GT (u + 1) (shiftr01 1 0 Z) := by
      have h := GT_loadTop (u := u + 1) (K := ([] : TrioSeq))
        (by intro y hy; simp at hy) (GT_nil (u + 1)) Z
        (Wg_mono (by omega) hZ) hb
      simpa using h
    have hWr : ∀ y ∈ shiftr01 1 0 Z, 1 ≤ y.1 := by
      intro y hy
      obtain ⟨p, -, rfl⟩ := mem_shiftr01.1 hy
      dsimp only; omega
    exact GT_nest hWgt hWr

end Gtrc4test
end TRIO
