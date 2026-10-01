/-
**`M[1]` は最後の列を落とす。標準形の接頭辞は標準形。**
-/
import Ytosk.BMS
import Ytosk.Bridge

namespace Ytosk

theorem take_append_cols (M : Mat) {r x : Nat} (hrx : r ≤ x) (hx : x ≤ M.length) :
    M.take r ++ (List.range (x - r)).map (fun k => (entry M 0 (r + k), entry M 1 (r + k), entry M 2 (r + k)))
      = M.take x := by
  have hd : (List.range (x - r)).map (fun k => (entry M 0 (r + k), entry M 1 (r + k), entry M 2 (r + k)))
      = (M.drop r).take (x - r) := by
    apply List.ext_getElem
    · simp; omega
    · intro k h1 h2
      simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
      have hk : r + k < M.length := by simp at h1; omega
      unfold entry
      simp only [List.getD, List.getElem?_eq_getElem hk, Option.getD_some]
      simp
  rw [hd, ← List.take_add]
  congr 1; omega

/-- **`M[1]` drops the last column.** -/
theorem expand_one (M : Mat) : expand M 1 = M.take (M.length - 1) := by
  cases M with
  | nil => rfl
  | cons c M' =>
    unfold expand
    simp only
    split_ifs with h
    all_goals first
      | rfl
      | (split
         · rfl
         · rename_i r hr
           have := par_lt _ _ _ _ hr
           simp only [List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.zero_mul,
             ite_self, Nat.add_zero]
           exact take_append_cols _ (by omega) (by omega))

/-- Dropping the last column keeps standardness. -/
theorem std_dropLast {M : Mat} (h : Std M) : Std (M.take (M.length - 1)) := by
  rw [← expand_one]; exact Std.exp 1 h

/-- **Every prefix of a standard matrix is standard.** -/
theorem std_take {M : Mat} (h : Std M) : ∀ j, j ≤ M.length → Std (M.take j) := by
  have key : ∀ m j, M.length - j ≤ m → j ≤ M.length → Std (M.take j) := by
    intro m
    induction m with
    | zero =>
      intro j hm hj
      rw [show j = M.length by omega, List.take_length]; exact h
    | succ m ih =>
      intro j hm hj
      rcases Nat.eq_or_lt_of_le hj with hjx | hjx
      · rw [hjx, List.take_length]; exact h
      · have hN := std_dropLast (ih (j + 1) (by omega) hjx)
        rwa [List.length_take, Nat.min_eq_left (by omega), show j + 1 - 1 = j by omega, List.take_take,
          Nat.min_eq_left (by omega)] at hN
  exact fun j hj => key (M.length - j) j (Nat.le_refl _) hj

end Ytosk
