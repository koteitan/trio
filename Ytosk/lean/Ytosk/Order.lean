/-
**項の辞書式順序は全順序。**

`lt` は (添字, 引数, 残り) の辞書式で、0 が最小。これを `<` として、Mathlib の `LinearOrder` を入れる。
-/
import Ytosk.Term
import Mathlib.Order.Defs.LinearOrder

namespace Ytosk

open T

instance : LT T := ⟨fun x y => lt x y = true⟩
instance : LE T := ⟨fun x y => lt x y = true ∨ x = y⟩

theorem lt_iff_lt (x y : T) : x < y ↔ lt x y = true := Iff.rfl

theorem le_iff (x y : T) : x ≤ y ↔ x < y ∨ x = y := Iff.rfl

namespace T

@[simp] theorem not_lt_z (x : T) : ¬ x < z := by
  cases x <;> simp [lt_iff_lt, lt]

@[simp] theorem z_lt_psi (a b c : T) : z < psi a b c := by
  simp [lt_iff_lt, lt]

theorem lt_irrefl' : ∀ x : T, ¬ x < x
  | z => by simp
  | psi a b c => by
    have := lt_irrefl' c
    simp only [lt_iff_lt, lt] at this ⊢
    exact this

/-- Comparison of two nonzero terms. -/
theorem psi_lt_psi {a b c d e f : T} :
    psi a b c < psi d e f ↔ a < d ∨ (a = d ∧ b < e) ∨ (a = d ∧ b = e ∧ c < f) := by
  simp only [lt_iff_lt, lt]
  by_cases h1 : a = d
  · subst h1
    by_cases h2 : b = e
    · subst h2
      have ha := lt_irrefl' a
      have hb := lt_irrefl' b
      simp only [lt_iff_lt] at ha hb
      simp [ha, hb]
    · have ha := lt_irrefl' a
      simp only [lt_iff_lt] at ha
      simp [h2, ha]
  · simp [h1]

theorem lt_trans' : ∀ {x y w : T}, x < y → y < w → x < w
  | z, y, w, hxy, hyw => by
    cases w with
    | z => exact absurd hyw (not_lt_z y)
    | psi => simp
  | psi a b c, y, w, hxy, hyw => by
    cases y with
    | z => exact absurd hxy (not_lt_z _)
    | psi d e f =>
      cases w with
      | z => exact absurd hyw (not_lt_z _)
      | psi g h i =>
        rw [psi_lt_psi] at hxy hyw ⊢
        rcases hxy with h1 | ⟨rfl, h1⟩ | ⟨rfl, rfl, h1⟩ <;>
          rcases hyw with h2 | ⟨rfl, h2⟩ | ⟨rfl, rfl, h2⟩
        · exact Or.inl (lt_trans' h1 h2)
        · exact Or.inl h1
        · exact Or.inl h1
        · exact Or.inl h2
        · exact Or.inr (Or.inl ⟨rfl, lt_trans' h1 h2⟩)
        · exact Or.inr (Or.inl ⟨rfl, h1⟩)
        · exact Or.inl h2
        · exact Or.inr (Or.inl ⟨rfl, h2⟩)
        · exact Or.inr (Or.inr ⟨rfl, rfl, lt_trans' h1 h2⟩)

theorem lt_trichotomy' : ∀ x y : T, x < y ∨ x = y ∨ y < x
  | z, z => Or.inr (Or.inl rfl)
  | z, psi _ _ _ => Or.inl (z_lt_psi _ _ _)
  | psi _ _ _, z => Or.inr (Or.inr (z_lt_psi _ _ _))
  | psi a b c, psi d e f => by
    rw [psi_lt_psi, psi_lt_psi]
    rcases lt_trichotomy' a d with h | rfl | h
    · exact Or.inl (Or.inl h)
    · rcases lt_trichotomy' b e with h | rfl | h
      · exact Or.inl (Or.inr (Or.inl ⟨rfl, h⟩))
      · rcases lt_trichotomy' c f with h | rfl | h
        · exact Or.inl (Or.inr (Or.inr ⟨rfl, rfl, h⟩))
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h⟩)))
    · exact Or.inr (Or.inr (Or.inl h))

end T

instance : DecidableRel (fun x y : T => x < y) := fun x y => inferInstanceAs (Decidable (lt x y = true))

instance : LinearOrder T where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl x := Or.inr rfl
  le_trans x y w hxy hyw := by
    rcases hxy with h1 | rfl
    · rcases hyw with h2 | rfl
      · exact Or.inl (T.lt_trans' h1 h2)
      · exact Or.inl h1
    · exact hyw
  lt_iff_le_not_ge x y := by
    constructor
    · intro h
      refine ⟨Or.inl h, ?_⟩
      rintro (h' | h')
      · exact T.lt_irrefl' x (T.lt_trans' h h')
      · subst h'; exact T.lt_irrefl' _ h
    · rintro ⟨h1 | rfl, h2⟩
      · exact h1
      · exact absurd (Or.inr rfl) h2
  le_antisymm x y hxy hyx := by
    rcases hxy with h1 | rfl
    · rcases hyx with h2 | rfl
      · exact absurd (T.lt_trans' h1 h2) (T.lt_irrefl' x)
      · rfl
    · rfl
  le_total x y := by
    rcases T.lt_trichotomy' x y with h | rfl | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr (Or.inl h)
  toDecidableLE := fun x y => inferInstanceAs (Decidable (lt x y = true ∨ x = y))

end Ytosk
