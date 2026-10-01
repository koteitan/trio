/-
**3 行の構造の不変条件は先頭部分で保たれる**（R0P・Z2・Z1C・SibDec）。UAT は別（q の topped が変わりうる）。
-/
import Ytosk.V3BaseT1

namespace Ytosk

open T

theorem entry_out {M : Mat} {k : Nat} (hk : M.length ≤ k) (i : Nat) : entry M i k = 0 := by
  unfold entry
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]
  split_ifs <;> rfl

theorem par0_out {M : Mat} {c p : Nat} (hc : M.length ≤ c) : par M 0 c ≠ some p := by
  intro h
  have := ((par0_spec M).mp h).2.1
  rw [entry_out hc] at this; omega

theorem R0P_take {M : Mat} (h : R0P M) (k : Nat) : R0P (M.take k) := by
  intro c p hp
  by_cases hc : c < (M.take k).length
  · have hck : c < k := by rw [List.length_take] at hc; omega
    have hpc := par_lt (M.take k) 0 c p hp
    rw [par_take M 0 c hck] at hp
    rw [entry_take M 0 hck, entry_take M 0 (by omega)]
    exact h c p hp
  · exact absurd hp (par0_out (by omega))

theorem Z2_take {M : Mat} (h : Z2 M) (k : Nat) : Z2 (M.take k) := by
  intro i
  by_cases hi : i < k
  · rw [entry_take M 2 hi]; exact h i
  · by_cases hl : (M.take k).length ≤ i
    · rw [entry_out hl]; omega
    · rw [List.length_take] at hl; omega

theorem Z1C_take {M : Mat} (h : Z1C M) (k : Nat) : Z1C (M.take k) := by
  intro p c hp hc
  rw [children_take, List.mem_filter] at hc
  have hck : c < k := by simpa using hc.2
  have hpc := (mem_children hc.1).1
  rw [entry_take M 1 hck, entry_take M 1 (by omega)]
  rw [entry_take M 2 (by omega)] at hp
  exact h p c hp hc.1

/-- Filtering a sorted list by `< k` keeps an initial segment. -/
theorem filter_lt_prefix : ∀ (l : List Nat) (k : Nat), l.Pairwise (· < ·) →
    ∃ rest, l = l.filter (fun c => decide (c < k)) ++ rest
  | [], _, _ => ⟨[], rfl⟩
  | a :: l, k, hs => by
    have hs' := (List.pairwise_cons.mp hs).2
    by_cases ha : a < k
    · obtain ⟨rest, hr⟩ := filter_lt_prefix l k hs'
      refine ⟨rest, ?_⟩
      rw [List.filter_cons_of_pos (by simpa using ha), List.cons_append, ← hr]
    · refine ⟨a :: l, ?_⟩
      have hnil : (a :: l).filter (fun c => decide (c < k)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro c hc hck
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ha (by simpa using hck)
        · have := (List.pairwise_cons.mp hs).1 c hc
          exact ha (by have := of_decide_eq_true hck; omega)
      rw [hnil]; rfl

theorem SibDec_take {M : Mat} (h : SibDec M) (k : Nat) : SibDec (M.take k) := by
  intro p l₁ l₂ a b hch
  rw [children_take] at hch
  obtain ⟨rest, hr⟩ := filter_lt_prefix (children M p) k (children_sorted M p)
  have hM : children M p = l₁ ++ a :: b :: (l₂ ++ rest) := by
    rw [hr, hch]; simp
  have ha : a ∈ (children M p).filter (fun c => decide (c < k)) := by
    rw [hch]; simp
  have hb : b ∈ (children M p).filter (fun c => decide (c < k)) := by
    rw [hch]; simp
  rw [List.mem_filter] at ha hb
  rw [col_take M (by simpa using hb.2), col_take M (by simpa using ha.2)]
  exact h p l₁ (l₂ ++ rest) a b hM

end Ytosk
