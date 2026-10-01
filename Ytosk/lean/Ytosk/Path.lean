/-
**行 0 の祖先と、最後の列への経路。**

- `par0_spec`: 行 0 の親の特徴づけ（前にある、行 0 が小さい、間の列は行 0 が親以上）。
- `Anc0`: 行 0 の祖先（反射推移閉包）。`anc0_interval`: 祖先と子孫の間の列は、行 0 が祖先より大きい。
- `children_le_of_anc_last`: 最後の列の祖先 p の親 h では、p が最後の子。
-/
import Ytosk.Prefix

namespace Ytosk

open T

/-- **The row-0 parent.** -/
theorem par0_spec (M : Mat) {a b : Nat} :
    par M 0 b = some a ↔
      a < b ∧ entry M 0 a < entry M 0 b ∧ ∀ j, a < j → j < b → entry M 0 b ≤ entry M 0 j := by
  cases b with
  | zero =>
    simp only [par, prev]
    constructor
    · intro h; simp [climb] at h
    · rintro ⟨h, _⟩; exact absurd h (Nat.not_lt_zero _)
  | succ c =>
    simp only [par, prev]
    rw [climb_prev_iff _ a c (c + 1 + 1) (by omega)]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by omega, by simpa using h2, fun j hj1 hj2 => ?_⟩
      have := h3 j hj1 (by omega)
      simpa using this
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by omega, by simpa using h2, fun j hj1 hj2 => ?_⟩
      simpa using h3 j hj1 (by omega)

/-- Row-0 ancestor (reflexive). -/
inductive Anc0 (M : Mat) : Nat → Nat → Prop
  | refl (b : Nat) : Anc0 M b b
  | step {a b c : Nat} : par M 0 c = some b → Anc0 M a b → Anc0 M a c

theorem Anc0.le {M : Mat} {a b : Nat} (h : Anc0 M a b) : a ≤ b := by
  induction h with
  | refl => exact Nat.le_refl _
  | step hp _ ih => have := par_lt M 0 _ _ hp; omega

/-- **Descendants form an interval**: between an ancestor and a descendant, row 0 is above the
ancestor's. -/
theorem anc0_interval {M : Mat} {a b : Nat} (h : Anc0 M a b) :
    ∀ j, a < j → j ≤ b → entry M 0 a < entry M 0 j := by
  induction h with
  | refl => intro j h1 h2; omega
  | @step b c hp hA ih =>
    intro j h1 h2
    have hab0 := hA.le
    obtain ⟨hbc, hlt, hbet⟩ := (par0_spec M).mp hp
    rcases Nat.lt_or_ge b j with hj | hj
    · -- `b < j ≤ c`: row 0 at `j` is at least that of `c`, above that of `b`
      have hjc : entry M 0 c ≤ entry M 0 j := by
        rcases Nat.lt_or_ge j c with h3 | h3
        · exact hbet j hj h3
        · have : j = c := by omega
          subst this; exact Nat.le_refl _
      have hab : entry M 0 a ≤ entry M 0 b := by
        rcases Nat.lt_or_ge a b with h4 | h4
        · exact Nat.le_of_lt (ih b h4 (Nat.le_refl _))
        · have : a = b := by omega
          subst this; exact Nat.le_refl _
      omega
    · exact ih j h1 hj

/-- A column after an ancestor of `b` and up to `b` has its row-0 parent at or after the ancestor. -/
theorem par0_ge_of_anc {M : Mat} {p b c h : Nat} (hA : Anc0 M p b) (hpc : p < c) (hcb : c ≤ b)
    (hc : par M 0 c = some h) : p ≤ h := by
  obtain ⟨hhc, hlt, hbet⟩ := (par0_spec M).mp hc
  have hp := anc0_interval hA c hpc hcb
  rcases Nat.lt_or_ge h p with h1 | h1
  · have := hbet p h1 hpc; omega
  · exact h1

/-- **On the way to the last column, the path child is the last child.** If `p` is a row-0 ancestor of
the last column `b` and `h` is the parent of `p`, every child of `h` is at most `p`. -/
theorem children_le_of_anc_last {M : Mat} {p b h : Nat} (hA : Anc0 M p b) (hb : b + 1 = M.length)
    (hp : par M 0 p = some h) : ∀ c ∈ children M h, c ≤ p := by
  intro c hc
  unfold children at hc
  rw [List.mem_filter] at hc
  obtain ⟨hc1, hc2⟩ := hc
  have hcl := List.mem_range.mp hc1
  have hpar : par M 0 c = some h := by simpa using hc2
  by_contra hcon
  have hpc : p < c := by omega
  have := par0_ge_of_anc hA hpc (by omega) hpar
  have := par_lt M 0 p h hp
  omega

end Ytosk
