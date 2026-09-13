/-
GwT.lean: 字の中身に行 2 の列を含む木と、シート行 377 以降。

`GwS.GOKR_of_Wg2` は字の中身 `T ∈ Wg 2` を任意に取れる。行 2 の列を含む中身
（例 `(1,1,0)(2,2,1)`）も、natDom の分岐で `Wg 2` に入れば字として継げる。
-/
import GwS

namespace TRIO
namespace GwT

open Wset
open Small
open GwS

/-- 空の語の対角の塔は階段。 -/
theorem Dzf_nil_eq (a b n : ℕ) :
    Dzf (fun a b => rword a b ([] : List TrioSeq)) a b n
      = (List.range n).map (fun k => ((a + k, b + k, 0) : ℕ × ℕ × ℕ)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Dzf_succ, ih, List.range_succ, List.map_append]; rfl

/-- 字の中身 `(1,1,0)(2,2,1)`。 -/
def T21 : TrioSeq := [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)]

theorem T21_eq : T21 = ([] : TrioSeq) ++
    (((1, 1, 0) : ℕ × ℕ × ℕ) :: rword 1 1 ([] : List TrioSeq) ++ [((2, 2, 1) : ℕ × ℕ × ℕ)]) :=
  rfl

theorem T21_le0 : le0 T21 0 1 :=
  ⟨by simp [T21], by simp [T21], Relation.ReflTransGen.single
    ⟨by simp [T21], by simp [T21], by omega, by simp [T21, entry], fun j hj => by omega⟩⟩

theorem T21_le1 : le1 T21 0 1 := by
  refine ⟨by simp [T21], by simp [T21], Relation.ReflTransGen.single
    ⟨by simp [T21], by simp [T21], by omega, by simp [T21, entry], T21_le0, fun j hj => ?_⟩⟩
  have hj1 : j ≤ 1 := rtg0_le hj.2.2.2
  have : j = 1 := by omega
  subst this
  exact le_rfl

theorem T21_natDom : natDom T21 := by
  refine natDom_iff.mpr (Or.inr ?_)
  have hsr : srow T21 (T21.length - 1) = 2 := by simp [srow, T21, entry]
  have hl : T21.length - 1 = 1 := by simp [T21]
  rw [hsr, hl]
  exact hasParent_two_of (by simp [T21]) (by omega) T21_le1 (by simp [T21, entry])

theorem T21_Wg : T21 ∈ Gw.Wg 2 := by
  refine Gw.A1g_intro (Or.inr (Or.inl ⟨T21_natDom, fun n _ => ?_⟩))
  rw [T21_eq, oper_z1wR [] 1 1 (by omega) (l := []) (by intro T hT; simp at hT) n,
    List.nil_append, Dzf_nil_eq]
  cases n with
  | zero => exact Gw.Wg_nil 2
  | succ m =>
      have e : (List.range (m + 1)).map (fun k => ((1 + k, 1 + k, 0) : ℕ × ℕ × ℕ))
          = ((1, 1, 0) : ℕ × ℕ × ℕ) ::
            (List.range m).map (fun i => ((i + 2, i + 2, 0) : ℕ × ℕ × ℕ)) := by
        rw [List.range_succ_eq_map, List.map_cons, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        exact Prod.ext (show 1 + (i + 1) = i + 2 by omega)
          (Prod.ext (show 1 + (i + 1) = i + 2 by omega) rfl)
      rw [e]
      have h := Gw.tree_mem_Wg (p0 := ((1, 1, 0) : ℕ × ℕ × ℕ))
        (R := (List.range m).map (fun i => ((i + 2, i + 2, 0) : ℕ × ℕ × ℕ)))
        (by
          intro p hp
          simp only [List.mem_cons, List.mem_map, List.mem_range] at hp
          rcases hp with rfl | ⟨i, -, rfl⟩ <;> rfl)
        (by
          intro q hq
          simp only [List.mem_map, List.mem_range] at hq
          obtain ⟨i, -, rfl⟩ := hq
          show 1 < i + 2; omega)
      exact h

theorem T21_ge : ∀ x ∈ T21, 1 ≤ x.1 := by
  intro x hx
  simp only [T21, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · show 1 ≤ 1; omega
  · show 1 ≤ 2; omega

theorem T21_mono : Mono T21 := by
  intro x hx
  simp only [T21, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · show (0 : ℕ) ≤ 1; omega
  · show (1 : ℕ) ≤ 2; omega

/-- ★ シート行 377 `(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,1) ∈ W 0`（仮定なし）。 -/
theorem R377_mem : R341 ++ [((3, 1, 0) : ℕ × ℕ × ℕ), ((4, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hG := GOKR_of_Wg2 T21 T21_Wg T21_ge T21_mono [] (by intro T hT; simp at hT)
    GoodFb_rword_nil
  have h := row_mem_of_GoodFb Aok_R338 hG
  have e : R338 ++ (((1, 1, 0) : ℕ × ℕ × ℕ) :: rword 1 1 ([] ++ [T21]))
      = R341 ++ [((3, 1, 0) : ℕ × ℕ × ℕ), ((4, 2, 1) : ℕ × ℕ × ℕ)] := by
    rfl
  rw [← e]; exact h

#print axioms R377_mem

end GwT
end TRIO
