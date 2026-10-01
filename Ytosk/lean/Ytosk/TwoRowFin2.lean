/-
**2 行の停止性（Ytosk の翻訳による）。**

- `inv2_expand_all`: Inv2 はすべての展開 M[n] で保たれる（(I1) と (I2) の場合分けをまとめたもの）。
- `twoRow_wf`: Inv2 の行列からの展開の関係は整礎（根の和 `ev2r` が標準形の項の中で真に下がり、`wf_OT`）。
-/
import Ytosk.TwoRowI3

namespace Ytosk

open T

set_option linter.unusedSectionVars false

theorem inv2_nil : Inv2 ([] : Mat) where
  g2 := good2_nil
  hi := by intro h p _ _ hp; simp at hp
  fc := by intro h p _ _ hp; simp at hp
  rd := by show ((roots ([] : Mat)).map (o2r [])).Pairwise _; exact List.Pairwise.nil
  z0 := by intro j hj; simp at hj
  r1 := by intro j hj; simp at hj
  e00 := rfl
  row2 := fun _ => rfl

/-- **The invariant survives every expansion.** -/
theorem inv2_expand_all {M : Mat} (hI : Inv2 M) (n : Nat) : Inv2 (expand M n) := by
  rcases Nat.lt_or_ge M.length 2 with hl | hM
  · rcases Nat.eq_zero_or_pos M.length with h0 | h1
    · have : M = [] := List.eq_nil_of_length_eq_zero h0
      subst this; exact inv2_nil
    · -- one column: it is a root, and the expansion is empty
      have hcol : col M (M.length - 1) = (0, 0, 0) := by
        have hx0 : entry M 0 (M.length - 1) = 0 := by rw [show M.length - 1 = 0 by omega]; exact hI.e00
        obtain ⟨e1, e2⟩ := hI.z0 (M.length - 1) (by omega) hx0
        unfold col
        have e0' : (M.getD (M.length - 1) (0, 0, 0)).1 = 0 := hx0
        rcases hc : M.getD (M.length - 1) (0, 0, 0) with ⟨a, b, c⟩
        rw [hc] at e0' e1 e2; simp at e0' e1 e2; rw [e0', e1, e2]
      rw [expand_zero_col h1 hcol n, show M.length - 1 = 0 by omega, List.take_zero]
      exact inv2_nil
  · by_cases hcol : col M (M.length - 1) = (0, 0, 0)
    · rw [expand_zero_col (by omega) hcol n]; exact inv2_take hI hM
    · have hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
          TRIO.entry M 2 (M.length - 1) = 0) := by
        rintro ⟨e0, e1, e2⟩; apply hcol; unfold col
        have e0' : (M.getD (M.length - 1) (0, 0, 0)).1 = 0 := e0
        have e1' : (M.getD (M.length - 1) (0, 0, 0)).2.1 = 0 := e1
        have e2' : (M.getD (M.length - 1) (0, 0, 0)).2.2 = 0 := e2
        rcases hc : M.getD (M.length - 1) (0, 0, 0) with ⟨a, b, c⟩
        rw [hc] at e0' e1' e2'; simp at e0' e1' e2'; rw [e0', e1', e2']
      have hx0 : 0 < entry M 0 (M.length - 1) := by
        rcases Nat.eq_zero_or_pos (entry M 0 (M.length - 1)) with h | h
        · exfalso; obtain ⟨e1, e2⟩ := hI.z0 (M.length - 1) (by omega) h; exact hz ⟨h, e1, e2⟩
        · exact h
      have hsrow : TRIO.srow M (M.length - 1) = if 0 < entry M 1 (M.length - 1) then 1 else 0 := by
        unfold TRIO.srow; rw [← entry_eq, ← entry_eq, hI.row2]; simp
      obtain ⟨r, hr⟩ : ∃ r, par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r := by
        rw [hsrow]
        split_ifs with hb
        · obtain ⟨m, hm, _⟩ := hI.g2.f1 _ hb; exact ⟨m, hm⟩
        · exact par0_some_of (show 0 < M.length - 1 by omega) (by rw [hI.e00]; exact hx0)
      have hrx := par_lt M _ _ _ hr
      rcases n with _ | _ | n
      · -- `M[0] = M.take r`
        rw [expand_n0 hM hz hr]
        rcases Nat.eq_zero_or_pos r with h0 | hpos
        · rw [h0, List.take_zero]; exact inv2_nil
        · exact inv2_take_all hI r hpos (by omega)
      · rw [expand_n1 hM hz hr]; exact inv2_take hI hM
      · by_cases hb : 0 < entry M 1 (M.length - 1)
        · have ht1 : TRIO.srow M (M.length - 1) = 1 := by rw [hsrow, if_pos hb]
          exact inv2_expand_t1_all hM hz hr ht1 hI (n + 2) (by omega)
        · have ht0 : TRIO.srow M (M.length - 1) = 0 := by rw [hsrow, if_neg hb]
          cases hg : par M 0 r with
          | none => exact inv2_expand_t0_root hM hz hr ht0 hI hg (by omega)
          | some g => exact inv2_expand_t0_g hM hz hr ht0 hI hg (by omega)

/-- With the invariant, the matrix value is standard. -/
theorem ev2r_ot {M : Mat} (hI : Inv2 M) : isOT (ev2r M) = true := by
  rw [ev2r_roots]
  exact (sumN_dec _ (fun t ht => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht; exact single_o2r hI.g2 i) hI.rd).1

/-- One expansion step from a matrix with the invariant. -/
def Step2 (N M : Mat) : Prop := Inv2 M ∧ 1 ≤ M.length ∧ ∃ n, N = expand M n

/-- **Two rows: expansion terminates from every matrix with the invariant.** -/
theorem twoRow_wf : WellFounded Step2 := by
  have main : ∀ t, Acc (fun s t : T => isOT s = true ∧ isOT t = true ∧ s < t) t →
      ∀ M, Inv2 M → ev2r M = t → Acc Step2 M := by
    intro t hacc
    induction hacc with
    | intro t _ ih =>
      intro M hI hev
      constructor
      rintro N ⟨_, hM, n, rfl⟩
      obtain ⟨hot, hlt⟩ := twoRow_desc_inv hM hI n
      exact ih (ev2r (expand M n)) ⟨hot, by rw [← hev]; exact ev2r_ot hI, by rw [← hev]; exact hlt⟩
        _ (inv2_expand_all hI n) rfl
  constructor
  intro M
  by_cases hI : Inv2 M
  · exact main _ (wf_OT.apply _) M hI rfl
  · constructor
    rintro N ⟨hI', _⟩
    exact absurd hI' hI

end Ytosk
