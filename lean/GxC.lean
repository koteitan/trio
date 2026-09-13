/-
GxC.lean: シート行 440 `(0,0,0)(1,1,1)(2,1,0)(1,1,1)(1,1,0)(2,2,1)(3,2,0)(2,2,1)`。

行 440 は台座 `Gm` の後ろに `Gm` を 1 段上げた塊 `L4 = (1,1,0)(2,2,1)(3,2,0)(2,2,1)` を継いだもの。
末尾 `(2,2,1)` の行 2 の親は `(1,1,0)` で、展開は `oper_z1_mask` で
`Gm ++ Σ_k Blk 0 (k+1) = Gm ++ TG n`。BH（`GwY.base_hang`、台座 `Aok_Gm`）で `W 0`。
-/
import GxA

namespace TRIO
namespace GxC

open Wset
open Small
open GwS
open Gw
open GwZ
open GxA

def L4 : TrioSeq := [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 2, 0) : ℕ × ℕ × ℕ),
  ((2, 2, 1) : ℕ × ℕ × ℕ)]

theorem TG_flat (n : ℕ) : TG n = (List.range n).flatMap (fun k => GwZ.Blk 0 (k + 1)) := by
  rw [TG, S_flat, GwV.shiftr01_flatMap]
  apply List.flatMap_congr
  intro j _
  exact shift_Blk 0 j

def L8 : TrioSeq := [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
  ((1, 1, 1) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
  ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)]

theorem L8_n45 : nextrel0 L8 4 5 :=
  ⟨by simp [L8], by simp [L8], by omega, by simp [L8, entry], fun j hj => by omega⟩

theorem L8_n56 : nextrel0 L8 5 6 :=
  ⟨by simp [L8], by simp [L8], by omega, by simp [L8, entry], fun j hj => by omega⟩

theorem L8_le1_5 : le1 L8 4 5 := by
  refine ⟨by simp [L8], by simp [L8], Relation.ReflTransGen.single
    ⟨by simp [L8], by simp [L8], by omega, by simp [L8, entry],
      ⟨by simp [L8], by simp [L8], Relation.ReflTransGen.single L8_n45⟩, fun j hj => ?_⟩⟩
  have h1 := rtg0_le hj.2.2.2
  have : j = 5 := by omega
  subst this
  exact le_rfl

theorem L8_le1_6 : le1 L8 4 6 := by
  refine ⟨by simp [L8], by simp [L8], Relation.ReflTransGen.single
    ⟨by simp [L8], by simp [L8], by omega, by simp [L8, entry],
      ⟨by simp [L8], by simp [L8],
        Relation.ReflTransGen.tail (Relation.ReflTransGen.single L8_n45) L8_n56⟩,
      fun j hj => ?_⟩⟩
  have h1 := rtg0_le hj.2.2.2
  rcases (by omega : j = 5 ∨ j = 6) with rfl | rfl <;> simp [L8, entry]

open Classical in
theorem oper_R440 (n : ℕ) :
    (Gm ++ L4)⟦n⟧ = Gm ++ (List.range n).flatMap (fun k => GwZ.Blk 0 (k + 1)) := by
  have h := oper_z1_mask Gm 1 1 [((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 2, 0) : ℕ × ℕ × ℕ)]
    (by decide) n
  have eM : Gm ++ L4 = Gm ++ (((1, 1, 0) : ℕ × ℕ × ℕ) :: [((2, 2, 1) : ℕ × ℕ × ℕ),
      ((3, 2, 0) : ℕ × ℕ × ℕ)] ++ [((1 + 1, 1 + 1, 1) : ℕ × ℕ × ℕ)]) := rfl
  rw [eM, h]
  congr 1
  apply List.flatMap_congr
  intro k _
  have hle1 : le1 [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
      ((1, 1, 1) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
      ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)] 4 5 := L8_le1_5
  have hle2 : le1 [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
      ((1, 1, 1) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
      ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)] 4 6 := L8_le1_6
  simp [List.range_succ, hle1, hle2, entry, GwZ.Blk, Gm, Nat.add_comm] <;> omega

/-- ★ シート行 440 `(0,0,0)(1,1,1)(2,1,0)(1,1,1)(1,1,0)(2,2,1)(3,2,0)(2,2,1)`。 -/
theorem R440_mem : Gm ++ L4 ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_R440, ← TG_flat]
  exact GwY.base_hang (TG n) (TG_Wg n) (TG_ge n) (TG_mono n) (TG_head n) Gm Aok_Gm

#print axioms R440_mem

end GxC
end TRIO
