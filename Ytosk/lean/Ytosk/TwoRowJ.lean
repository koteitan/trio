/-
**2 行の不変条件 Inv2 と、仮定を減らした降下。**

Inv2 = Good2・PreHi・PreFC・RootsDec・z0ok・r1ok・左上が 0・行 2 が 0。
(I1) で最後の列を落としても保たれるので、すべての先頭部分で成り立つ（`inv2_take_all`）。
PRE は PreHi から、始点の条件は `seed_of_drop` から出るので、降下 `twoRow_desc` の仮定は Inv2 だけになる
（`twoRow_desc_inv`）。
-/
import Ytosk.TwoRowK

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The two-row invariant.** -/
structure Inv2 (M : Mat) : Prop where
  g2 : Good2 M
  hi : PreHi M
  fc : PreFC M
  rd : RootsDec M
  z0 : TRIO.z0ok M
  r1 : TRIO.r1ok M
  e00 : entry M 0 0 = 0
  row2 : ∀ j, entry M 2 j = 0

/-- **(I1) The invariant survives dropping the last column.** -/
theorem inv2_take {M : Mat} (hI : Inv2 M) (hM : 2 ≤ M.length) : Inv2 (M.take (M.length - 1)) where
  g2 := good2_take hM hI.g2 hI.hi hI.fc
  hi := preHi_take hM hI.g2 hI.hi hI.fc
  fc := preFC_take hM hI.g2 hI.hi hI.fc
  rd := rootsDec_take hM hI.g2 hI.hi hI.fc hI.rd hI.z0 hI.e00
  z0 := TRIO.z0ok_take hI.z0 _
  r1 := TRIO.r1ok_take hI.r1 _
  e00 := by rw [entry_take M 0 (show 0 < M.length - 1 by omega)]; exact hI.e00
  row2 := by
    intro j
    by_cases hj : j < M.length - 1
    · rw [entry_take M 2 hj]; exact hI.row2 j
    · unfold entry
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl

/-- The invariant on every nonempty prefix. -/
theorem inv2_take_all {M : Mat} (hI : Inv2 M) : ∀ j, 1 ≤ j → j ≤ M.length → Inv2 (M.take j) := by
  have key : ∀ m j, M.length - j ≤ m → 1 ≤ j → j ≤ M.length → Inv2 (M.take j) := by
    intro m
    induction m with
    | zero =>
      intro j h1 _ h3
      rw [show j = M.length by omega, List.take_length]; exact hI
    | succ m ih =>
      intro j h1 hm h3
      rcases Nat.eq_or_lt_of_le h3 with h | h
      · rw [h, List.take_length]; exact hI
      · have hI' := ih (j + 1) (by omega) (by omega) h
        have hl : (M.take (j + 1)).length = j + 1 := by rw [List.length_take]; omega
        have := inv2_take hI' (by rw [hl]; omega)
        rwa [hl, show j + 1 - 1 = j by omega, List.take_take, Nat.min_eq_left (by omega)] at this
  exact fun j h1 h3 => key _ j (Nat.le_refl _) h1 h3

theorem good2_nil : Good2 ([] : Mat) where
  f1 := by
    intro j hj
    exfalso
    have : entry ([] : Mat) 1 j = 0 := rfl
    omega
  ot := by intro i; rw [o2r_out (by simp)]; rfl
  dec := by
    intro h
    have : children ([] : Mat) h = [] := rfl
    rw [this]; exact List.Pairwise.nil

/-- The row-1 parent has a smaller row-1 entry. -/
theorem par1_entry_lt {M : Mat} {x r : Nat} (hr : par M 1 x = some r) : entry M 1 r < entry M 1 x := by
  have hr' : climb (par M 0) (fun q => decide (entry M 1 q < entry M 1 x)) (x + 1) (par M 0 x) =
      some r := hr
  cases hq : par M 0 x with
  | none => rw [hq] at hr'; simp [climb_none] at hr'
  | some q0 =>
    rw [hq] at hr'
    have hq0 := par_lt M 0 x q0 hq
    have := (climb_chain_iff (par M 0) _ (par_lt M 0) r (x + 1) q0 (by omega)).mp hr'
    simpa using this.2.1

/-- **Two rows: one expansion step lowers the matrix value, assuming only the invariant.** -/
theorem twoRow_desc_inv {M : Mat} (hM : 1 ≤ M.length) (hI : Inv2 M) (n : Nat) :
    isOT (ev2r (expand M n)) = true ∧ ev2r (expand M n) < ev2r M := by
  apply twoRow_desc hM (hI.row2 _) _ hI.r1 hI.z0 hI.e00 _ _ n
  · intro j hj
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      refine ⟨good2_nil, ?_, ?_⟩
      · show ((roots ([] : Mat)).map (o2r [])).Pairwise _
        have : roots ([] : Mat) = [] := rfl
        rw [this]; exact List.Pairwise.nil
      · intro i hi; simp at hi
    · have hIj := inv2_take_all hI j hpos hj
      exact ⟨hIj.g2, hIj.rd, hIj.z0⟩
  · intro h p s y hp hph hc h1 h2 h3
    have hpl : p < M.length := by have := hp.le; omega
    obtain ⟨hhi, hlo⟩ := hI.hi h p s y hpl hph hc h3 h1 h2
    refine ⟨loP s y, ?_, hlo⟩
    have := hiP_loP s y; rw [hhi] at this; exact this.symm
  · intro r hr1 _ a' ha' hot
    have hrx := par_lt M 1 _ r hr1
    have hM2 : 2 ≤ M.length := by omega
    have hb1 : 0 < entry M 1 (M.length - 1) := by have := par1_entry_lt hr1; omega
    have hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
        TRIO.entry M 2 (M.length - 1) = 0) := by
      rintro ⟨_, h1, _⟩; rw [← entry_eq] at h1; omega
    have ht1 : TRIO.srow M (M.length - 1) = 1 := by
      unfold TRIO.srow; rw [← entry_eq, ← entry_eq, hI.row2, if_neg (by omega), if_pos hb1]
    have hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r := by rw [ht1]; exact hr1
    rw [expand_n1 hM2 hz hr]
    exact seed_of_drop hM2 hI.g2 hI.hi hI.fc hr1 hb1 a' ha' hot

end Ytosk
