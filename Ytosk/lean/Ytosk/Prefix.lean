/-
**先頭部分 M.take k での行列の関数。**

親（すべての行）は前の列しか見ないので変わらない。子は k 未満に制限される。上げは最後の列以外で変わらない。
段 1 の不変条件（すべての先頭部分の評価が標準形）と、先頭部分の降下に使う。
-/
import Ytosk.Val

namespace Ytosk

open T

theorem entry_take (M : Mat) {l q : Nat} (i : Nat) (hq : q < l) : entry (M.take l) i q = entry M i q := by
  unfold entry
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hq]

theorem col_take (M : Mat) {l q : Nat} (hq : q < l) : col (M.take l) q = col M q := by
  unfold col
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hq]

theorem bump_take (M : Mat) {l q : Nat} (hq : q < l) : bump (M.take l) q = bump M q := by
  simp only [bump, entry_take M _ hq]

/-- `climb` only reads the steps and the test below a bound that the walk never leaves. -/
theorem climb_congr {s₁ s₂ : Nat → Option Nat} {ok₁ ok₂ : Nat → Bool} (B : Nat)
    (hs : ∀ q, q < B → s₁ q = s₂ q) (hok : ∀ q, q < B → ok₁ q = ok₂ q)
    (hdec : ∀ q q', s₁ q = some q' → q' < q) :
    ∀ f st, (∀ q, st = some q → q < B) → climb s₁ ok₁ f st = climb s₂ ok₂ f st
  | 0, _, _ => rfl
  | _ + 1, none, _ => rfl
  | f + 1, some q, hst => by
    have hq := hst q rfl
    simp only [climb]
    rw [hok q hq, ← hs q hq]
    split
    · rfl
    · apply climb_congr B hs hok hdec f
      intro q' hq'
      exact Nat.lt_trans (hdec q q' hq') hq

/-- **Parents in a prefix.** -/
theorem par_take (M : Mat) {k : Nat} : ∀ (r i : Nat), i < k → par (M.take k) r i = par M r i
  | 0, i, hi => by
    simp only [par]
    apply climb_congr (i + 1) (fun _ _ => rfl)
    · intro q hq; rw [entry_take M 0 (by omega), entry_take M 0 hi]
    · intro q q' h; cases q <;> simp [prev] at h; omega
    · intro q h; cases i <;> simp [prev] at h; omega
  | r + 1, i, hi => by
    simp only [par]
    rw [par_take M r i hi]
    apply climb_congr (i + 1)
    · intro q hq; exact par_take M r q (by omega)
    · intro q hq; rw [entry_take M (r + 1) (by omega), entry_take M (r + 1) hi]
    · exact par_lt (M.take k) r
    · intro q h; have := par_lt M r i q h; omega

theorem range_filter_lt (k : Nat) : ∀ n, (List.range n).filter (fun c => decide (c < k)) = List.range (min k n)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, range_filter_lt k n]
    by_cases h : n < k
    · have : min k (n + 1) = min k n + 1 := by omega
      rw [this, List.range_succ, show min k n = n by omega]; simp [h]
    · have : min k (n + 1) = min k n := by omega
      rw [this]; simp [h]

/-- **Children in a prefix.** -/
theorem children_take (M : Mat) (k i : Nat) :
    children (M.take k) i = (children M i).filter (fun c => decide (c < k)) := by
  unfold children
  rw [List.length_take, List.filter_comm, range_filter_lt k M.length]
  apply List.filter_congr
  intro c hc
  rw [par_take M 0 c (by have := List.mem_range.mp hc; omega)]

/-- **Upgrades in a prefix**, away from its last column. -/
theorem upg_take (M : Mat) {k i : Nat} (hi : i + 1 < k) : upg (M.take k) i = upg M i := by
  have hlen : (i + 1 = (M.take k).length) ↔ (i + 1 = M.length) := by
    rw [List.length_take]; omega
  unfold upg
  rw [entry_take M 1 (by omega), entry_take M 2 (by omega), par_take M 1 i (by omega)]
  have hc : (entry M 1 i = 0 ∨ entry M 2 i = 1 ∨ i + 1 = (M.take k).length) ↔
      (entry M 1 i = 0 ∨ entry M 2 i = 1 ∨ i + 1 = M.length) := by rw [hlen]
  by_cases h : entry M 1 i = 0 ∨ entry M 2 i = 1 ∨ i + 1 = M.length
  · rw [if_pos (hc.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]
    split
    · rfl
    · rename_i m _
      simp only
      rw [par_take M 1 (i + 1) hi, col_take M hi, entry_take M 0 (show m < k by
        have := par_lt M 1 i m (by assumption); omega), entry_take M 2 (show m < k by
        have := par_lt M 1 i m (by assumption); omega), par_take M 0 i (by omega)]
      congr 1
      apply climb_congr (i + 1)
      · intro q hq; exact par_take M 0 q (by omega)
      · intro q hq
        rw [par_take M 1 q (by omega), col_take M (by omega), entry_take M 0 (show q < k by omega),
          entry_take M 0 hi]
      · exact par_lt (M.take k) 0
      · intro q h; have := par_lt M 0 i q h; omega

/-- At the last column of a prefix there is no upgrade. -/
theorem upg_take_last (M : Mat) {k : Nat} (hk : k ≤ M.length) (hk1 : 1 ≤ k) :
    upg (M.take k) (k - 1) = none := by
  unfold upg
  rw [if_pos (Or.inr (Or.inr (by rw [List.length_take]; omega)))]

/-- Upgrades into a column of a prefix come from the columns before its last one. -/
theorem isUpg_take (M : Mat) {k : Nat} (hk : k ≤ M.length) (c : Nat) :
    isUpg (M.take k) c = true ↔ ∃ j, j + 1 < k ∧ upg M j = some c := by
  unfold isUpg
  rw [List.any_eq_true, List.length_take, show min k M.length = k by omega]
  constructor
  · rintro ⟨j, hj, h⟩
    have hj' := List.mem_range.mp hj
    have h' : upg (M.take k) j = some c := of_decide_eq_true h
    by_cases hjk : j + 1 < k
    · exact ⟨j, hjk, by rw [← upg_take M hjk]; exact h'⟩
    · have : j = k - 1 := by omega
      subst this
      rw [upg_take_last M hk (by omega)] at h'; cases h'
  · rintro ⟨j, hjk, h⟩
    exact ⟨j, List.mem_range.mpr (by omega), decide_eq_true (by rw [upg_take M hjk]; exact h)⟩

end Ytosk
