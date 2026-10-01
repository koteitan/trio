/-
**整礎性の証明の土台: 段・Ω・後続・α⁺・連結と、その順序の性質。**

- `lev t`: t の先頭の主項の添字（0 なら 0）。
- `Om ν` = Ω_ν = ψ_ν(0)。`succ ν` = ν + 1（末尾に 1 = ψ_0(0) を足す）。
- `plus α` = α⁺ = Ω_{lev α + 1}。
- `app x y`: リストとしての連結（和 x + y、非増加なら標準形の和）。
-/
import Ytosk.Order
import Ytosk.OT

namespace Ytosk

open T

/-- The subscript of the leading summand (`0` for `0`). -/
def lev : T → T
  | z => z
  | psi a _ _ => a

/-- `Ω_ν = ψ_ν(0)`. -/
def Om (ν : T) : T := psi ν z z

/-- Concatenation of the summand lists. -/
def app : T → T → T
  | z, y => y
  | psi a b c, y => psi a b (app c y)

/-- `ν + 1`. -/
def succ (ν : T) : T := app ν one

/-- `α⁺ = Ω_{lev α + 1}`, the least regular term above `α`. -/
def plus (α : T) : T := Om (succ (lev α))

/-- The number of constructors. -/
def size : T → Nat
  | z => 0
  | psi a b c => size a + size b + size c + 1

@[simp] theorem lev_z : lev z = z := rfl
@[simp] theorem lev_psi (a b c : T) : lev (psi a b c) = a := rfl
@[simp] theorem app_z (y : T) : app z y = y := rfl
@[simp] theorem app_psi (a b c y : T) : app (psi a b c) y = psi a b (app c y) := rfl

@[simp] theorem app_z_right : ∀ x : T, app x z = x
  | z => rfl
  | psi a b c => by simp [app_z_right c]

theorem size_app : ∀ x y : T, size (app x y) = size x + size y
  | z, y => by simp [size]
  | psi a b c, y => by simp [size, size_app c y]; omega

theorem app_ne_z_left {x y : T} (hx : x ≠ z) : app x y ≠ z := by
  cases x with
  | z => exact absurd rfl hx
  | psi => simp

theorem lev_app {x : T} (y : T) (hx : x ≠ z) : lev (app x y) = lev x := by
  cases x with
  | z => exact absurd rfl hx
  | psi => rfl

theorem plus_app {x : T} (y : T) (hx : x ≠ z) : plus (app x y) = plus x := by
  simp [plus, lev_app y hx]

/-! ## 順序の基本 -/

theorem lt_psi_z_iff {a b d e f : T} :
    psi a b z < psi d e f ↔ a < d ∨ (a = d ∧ b < e) ∨ (a = d ∧ b = e ∧ f ≠ z) := by
  rw [T.psi_lt_psi]
  cases f with
  | z => simp
  | psi => simp

theorem psi_lt_psi_z_iff {a b c d e : T} :
    psi a b c < psi d e z ↔ a < d ∨ (a = d ∧ b < e) := by
  rw [T.psi_lt_psi]; simp

/-- Every nonzero term is at least `1`. -/
theorem one_le_of_ne_z {t : T} (h : t ≠ z) : one ≤ t := by
  cases t with
  | z => exact absurd rfl h
  | psi a b c =>
    rw [le_iff, one, T.psi_lt_psi]
    rcases lt_trichotomy z a with h1 | h1 | h1
    · exact Or.inl (Or.inl h1)
    · subst h1
      rcases lt_trichotomy z b with h2 | h2 | h2
      · exact Or.inl (Or.inr (Or.inl ⟨rfl, h2⟩))
      · subst h2
        cases c with
        | z => exact Or.inr rfl
        | psi => exact Or.inl (Or.inr (Or.inr ⟨rfl, rfl, T.z_lt_psi _ _ _⟩))
      · exact absurd h2 (T.not_lt_z _)
    · exact absurd h1 (T.not_lt_z _)

theorem lt_one_iff {t : T} : t < one ↔ t = z := by
  constructor
  · intro h
    by_contra hne
    exact absurd h (not_lt_of_ge (one_le_of_ne_z hne))
  · rintro rfl; exact T.z_lt_psi _ _ _

theorem lt_succ_iff : ∀ {t x : T}, t < succ x ↔ t ≤ x
  | t, z => by
    simp only [succ, app_z]
    rw [lt_one_iff, le_iff]
    constructor
    · intro h; exact Or.inr h
    · rintro (h | h)
      · exact absurd h (T.not_lt_z _)
      · exact h
  | z, psi d e f => by
    simp only [succ, app_psi]
    exact ⟨fun _ => Or.inl (T.z_lt_psi _ _ _), fun _ => T.z_lt_psi _ _ _⟩
  | psi a b c, psi d e f => by
    simp only [succ, app_psi]
    have ih : c < app f one ↔ c ≤ f := lt_succ_iff
    rw [T.psi_lt_psi, le_iff, T.psi_lt_psi]
    constructor
    · rintro (h | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl ⟨rfl, h⟩))
      · rcases (ih.mp h) with h | rfl
        · exact Or.inl (Or.inr (Or.inr ⟨rfl, rfl, h⟩))
        · exact Or.inr rfl
    · rintro ((h | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨rfl, h⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl, ih.mpr (Or.inl h)⟩)
      · cases h; exact Or.inr (Or.inr ⟨rfl, rfl, ih.mpr (Or.inr rfl)⟩)

theorem lt_succ_self (x : T) : x < succ x := lt_succ_iff.mpr (le_refl x)

theorem succ_le_of_lt {x y : T} (h : x < y) : succ x ≤ y := by
  rcases le_or_gt (succ x) y with h1 | h1
  · exact h1
  · exact absurd (lt_succ_iff.mp h1) (not_le_of_gt h)

theorem lt_of_succ_lt_succ {x y : T} (h : succ x < succ y) : x < y :=
  lt_of_lt_of_le (lt_succ_self x) (lt_succ_iff.mp h)

@[simp] theorem om_lt_om {a b : T} : Om a < Om b ↔ a < b := by
  rw [Om, Om, T.psi_lt_psi]; simp

theorem om_le_om {a b : T} : Om a ≤ Om b ↔ a ≤ b := by
  rw [le_iff, le_iff, om_lt_om]; simp [Om]

/-- `t < Ω_μ` iff `t = 0` or the level of `t` is below `μ`. -/
theorem lt_om_iff {t μ : T} : t < Om μ ↔ t = z ∨ lev t < μ := by
  cases t with
  | z => simp [Om]
  | psi a b c => rw [Om, T.psi_lt_psi]; simp

/-- `t < α⁺` iff the level of `t` is at most that of `α`. -/
theorem lt_plus_iff {t α : T} : t < plus α ↔ lev t ≤ lev α := by
  rw [plus, lt_om_iff, lt_succ_iff]
  constructor
  · rintro (rfl | h)
    · rcases lt_trichotomy z (lev α) with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (T.not_lt_z _)
    · exact h
  · intro h; exact Or.inr h

theorem lt_plus_self (α : T) : α < plus α := lt_plus_iff.mpr (le_refl _)

theorem lev_le_of_le {t s : T} (h : t ≤ s) : lev t ≤ lev s := by
  cases t with
  | z =>
    rcases lt_trichotomy z (lev s) with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
    · exact absurd h' (T.not_lt_z _)
  | psi a b c =>
    cases s with
    | z =>
      rcases (le_iff _ _).mp h with h | h
      · exact absurd h (T.not_lt_z _)
      · cases h
    | psi d e f =>
      rcases (le_iff _ _).mp h with h | h
      · rw [T.psi_lt_psi] at h
        rcases h with h | ⟨rfl, _⟩ | ⟨rfl, _, _⟩
        · exact Or.inl h
        · exact le_refl _
        · exact le_refl _
      · cases h; exact le_refl _

theorem plus_le_plus {t s : T} (h : t ≤ s) : plus t ≤ plus s := by
  rw [plus, plus, om_le_om]
  rcases (le_iff _ _).mp (lev_le_of_le h) with h | h
  · exact le_of_lt (lt_of_le_of_lt (succ_le_of_lt h) (lt_succ_self _))
  · rw [h]

theorem om_lev_le {t : T} (h : t ≠ z) : Om (lev t) ≤ t := by
  cases t with
  | z => exact absurd rfl h
  | psi a b c =>
    rw [Om, lev_psi, le_iff, T.psi_lt_psi]
    rcases lt_trichotomy z b with h1 | h1 | h1
    · exact Or.inl (Or.inr (Or.inl ⟨rfl, h1⟩))
    · subst h1
      cases c with
      | z => exact Or.inr rfl
      | psi => exact Or.inl (Or.inr (Or.inr ⟨rfl, rfl, T.z_lt_psi _ _ _⟩))
    · exact absurd h1 (T.not_lt_z _)

/-- `β⁺ < η⁺` gives `β⁺ ≤ η`. -/
theorem plus_le_of_plus_lt {β η : T} (h : plus β < plus η) : plus β ≤ η := by
  rw [plus, plus, om_lt_om] at h
  have h1 : lev β < lev η := lt_of_succ_lt_succ h
  have hne : η ≠ z := by
    rintro rfl; exact absurd h1 (T.not_lt_z _)
  exact le_trans (om_le_om.mpr (succ_le_of_lt h1)) (om_lev_le hne)

/-- The subscript is below the term. -/
theorem sub_lt : ∀ (a b c : T), a < psi a b c
  | z, _, _ => T.z_lt_psi _ _ _
  | psi a1 a2 a3, b, c => by
    rw [T.psi_lt_psi]; exact Or.inl (sub_lt a1 a2 a3)

theorem sub_lt_om (a : T) : a < Om a := sub_lt a z z

theorem lev_lt_of_ne_z {t : T} (h : t ≠ z) : lev t < t := by
  cases t with
  | z => exact absurd rfl h
  | psi a b c => exact sub_lt a b c

end Ytosk
