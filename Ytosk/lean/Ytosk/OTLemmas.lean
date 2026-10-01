/-
**標準形 OT の性質と、連結・成分の補題。**
-/
import Ytosk.Basic

namespace Ytosk

open T

theorem le_bool_iff (x y : T) : le x y = true ↔ x ≤ y := by
  simp only [le, Bool.or_eq_true, beq_iff_eq, le_iff, lt_iff_lt]
  exact Or.comm

theorem z_le (x : T) : z ≤ x := by
  cases x with
  | z => exact le_refl _
  | psi => exact le_of_lt (T.z_lt_psi _ _ _)

/-- Unfolding `isOT` of a nonzero term. -/
theorem isOT_psi_iff {a b c : T} :
    isOT (psi a b c) = true ↔
      isOT a = true ∧ isOT b = true ∧ isOT c = true ∧ head c ≤ psi a b z ∧
        ∀ g ∈ comps a b, g < b := by
  cases c with
  | z => simp [isOT, head, z_le, List.all_eq_true, lt_iff_lt, and_assoc]
  | psi a' b' c' =>
    simp [isOT, head, le_bool_iff, List.all_eq_true, lt_iff_lt, and_assoc]

@[simp] theorem isOT_z : isOT z = true := rfl

theorem isOT_om {ν : T} : isOT (Om ν) = true ↔ isOT ν = true := by
  rw [Om, isOT_psi_iff]
  simp [head, comps, z_le]

theorem isOT_one : isOT one = true := by decide

theorem isOT_head {a b c : T} (h : isOT (psi a b c) = true) : isOT (psi a b z) = true := by
  rw [isOT_psi_iff] at h ⊢
  exact ⟨h.1, h.2.1, rfl, by simp [head, z_le], h.2.2.2.2⟩

theorem isOT_sub {a b c : T} (h : isOT (psi a b c) = true) : isOT a = true :=
  (isOT_psi_iff.mp h).1

theorem isOT_arg {a b c : T} (h : isOT (psi a b c) = true) : isOT b = true :=
  (isOT_psi_iff.mp h).2.1

theorem isOT_rest {a b c : T} (h : isOT (psi a b c) = true) : isOT c = true :=
  (isOT_psi_iff.mp h).2.2.1

theorem comps_lt {a b c : T} (h : isOT (psi a b c) = true) : ∀ g ∈ comps a b, g < b :=
  (isOT_psi_iff.mp h).2.2.2.2

/-- The rest of a standard term is below it. -/
theorem rest_lt : ∀ {a b c : T}, isOT (psi a b c) = true → c < psi a b c
  | a, b, z, _ => T.z_lt_psi _ _ _
  | a, b, psi a' b' c', h => by
    have hs : head (psi a' b' c') ≤ psi a b z := (isOT_psi_iff.mp h).2.2.2.1
    simp only [head] at hs
    rw [T.psi_lt_psi]
    rcases (le_iff _ _).mp hs with hlt | heq
    · rw [psi_lt_psi_z_iff] at hlt
      rcases hlt with ha | ⟨hae, hb⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl ⟨hae, hb⟩)
    · cases heq
      exact Or.inr (Or.inr ⟨rfl, rfl, rest_lt (isOT_rest h)⟩)

/-! ## 連結 -/

theorem isOT_app_left : ∀ {x y : T}, isOT (app x y) = true → isOT x = true
  | z, _, _ => rfl
  | psi a b c, y, h => by
    rw [app_psi, isOT_psi_iff] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have hc : isOT c = true := isOT_app_left h3
    rw [isOT_psi_iff]
    refine ⟨h1, h2, hc, ?_, h5⟩
    cases c with
    | z => simp [head, z_le]
    | psi a' b' c' => simpa [head] using h4

theorem isOT_app_right : ∀ {x y : T}, isOT (app x y) = true → isOT y = true
  | z, _, h => h
  | psi _ _ c, _, h => by
    rw [app_psi] at h
    exact isOT_app_right (isOT_rest h)

/-- The last principal summand of `x` is at least `1` when `x ≠ 0`. -/
theorem head_app_of_ne {x : T} (y : T) (hx : x ≠ z) : head (app x y) = head x := by
  cases x with
  | z => exact absurd rfl hx
  | psi => rfl

/-- Appending `1` keeps a standard term standard. -/
theorem isOT_succ : ∀ {ν : T}, isOT ν = true → isOT (succ ν) = true
  | z, _ => isOT_one
  | psi a b c, h => by
    simp only [succ, app_psi]
    have hc : isOT (succ c) = true := isOT_succ (isOT_rest h)
    rw [isOT_psi_iff] at h ⊢
    obtain ⟨h1, h2, _, h4, h5⟩ := h
    refine ⟨h1, h2, hc, ?_, h5⟩
    cases c with
    | z =>
      simp only [app_z, one, head]
      exact one_le_of_ne_z (by simp)
    | psi a' b' c' => simpa [succ, head] using h4

theorem lt_app_left : ∀ {x y : T}, x ≠ z → y ≠ z → x < app x y
  | z, _, hx, _ => absurd rfl hx
  | psi a b z, y, _, hy => by
    rw [app_psi, app_z, T.psi_lt_psi]
    right; right
    refine ⟨rfl, rfl, ?_⟩
    cases y with
    | z => exact absurd rfl hy
    | psi => exact T.z_lt_psi _ _ _
  | psi a b (psi a' b' c'), y, _, hy => by
    rw [app_psi, T.psi_lt_psi]
    exact Or.inr (Or.inr ⟨rfl, rfl, lt_app_left (by simp) hy⟩)

/-- In a standard sum, the second part is below the whole. -/
theorem lt_app_right : ∀ {x y : T}, isOT (app x y) = true → x ≠ z → y < app x y
  | z, _, _, hx => absurd rfl hx
  | psi a b c, y, h, _ => by
    rw [app_psi] at h ⊢
    by_cases hc : c = z
    · subst hc
      simp only [app_z] at h ⊢
      exact rest_lt h
    · have ih : y < app c y := lt_app_right (isOT_rest h) hc
      exact lt_trans ih (rest_lt h)

/-- Between `x` and `x + y` there are only `x + d'` with `d' < y`. -/
theorem decomp : ∀ {x y d : T}, x ≠ z → x < d → d < app x y → ∃ d', d = app x d' ∧ d' < y
  | z, _, _, hx, _, _ => absurd rfl hx
  | psi a b c, y, d, _, h1, h2 => by
    cases d with
    | z => exact absurd h1 (T.not_lt_z _)
    | psi a1 b1 c1 =>
      rw [app_psi] at h2
      rw [T.psi_lt_psi] at h1 h2
      have hab : a1 = a ∧ b1 = b := by
        rcases h1 with h1 | ⟨rfl, h1⟩ | ⟨rfl, rfl, _⟩ <;>
          rcases h2 with h2 | ⟨h2e, h2⟩ | ⟨h2e, h2f, _⟩
        · exact absurd (lt_trans h1 h2) (lt_irrefl _)
        · exact absurd (h2e ▸ h1) (lt_irrefl _)
        · exact absurd (h2e ▸ h1) (lt_irrefl _)
        · exact absurd h2 (lt_irrefl _)
        · exact absurd (lt_trans h1 h2) (lt_irrefl _)
        · exact absurd (h2f ▸ h1) (lt_irrefl _)
        · exact absurd h2 (lt_irrefl _)
        · exact absurd h2 (lt_irrefl _)
        · exact ⟨rfl, rfl⟩
      obtain ⟨rfl, rfl⟩ := hab
      have hc1 : c < c1 := by
        rcases h1 with h1 | ⟨_, h1⟩ | ⟨_, _, h1⟩
        · exact absurd h1 (lt_irrefl _)
        · exact absurd h1 (lt_irrefl _)
        · exact h1
      have hc2 : c1 < app c y := by
        rcases h2 with h2 | ⟨_, h2⟩ | ⟨_, _, h2⟩
        · exact absurd h2 (lt_irrefl _)
        · exact absurd h2 (lt_irrefl _)
        · exact h2
      by_cases hc : c = z
      · subst hc
        exact ⟨c1, by simp, by simpa using hc2⟩
      · obtain ⟨d', rfl, hd'⟩ := decomp hc hc1 hc2
        exact ⟨d', by simp, hd'⟩

/-! ## 成分 -/

theorem comps_app (u : T) : ∀ x y : T, comps u (app x y) = comps u x ++ comps u y
  | z, y => by simp [comps]
  | psi v x c, y => by simp [comps, comps_app u c y, List.append_assoc]

theorem comps_psi_z_of_ge {u v c : T} (h : ¬ v < u) :
    comps u (psi v c z) = c :: (comps u c ++ comps u v) := by
  have h' : lt v u = false := by simpa [lt_iff_lt] using h
  simp [comps, h']

theorem size_lt_app_left {x y : T} (hy : y ≠ z) : size x < size (app x y) := by
  rw [size_app]
  cases y with
  | z => exact absurd rfl hy
  | psi => simp [size]

theorem size_lt_app_right {x y : T} (hx : x ≠ z) : size y < size (app x y) := by
  rw [size_app]
  cases x with
  | z => exact absurd rfl hx
  | psi => simp [size]

theorem size_sub_lt (a b c : T) : size a < size (psi a b c) := by simp [size]; omega
theorem size_arg_lt (a b c : T) : size b < size (psi a b c) := by simp [size]; omega
theorem size_rest_lt (a b c : T) : size c < size (psi a b c) := by simp [size]; omega

end Ytosk
