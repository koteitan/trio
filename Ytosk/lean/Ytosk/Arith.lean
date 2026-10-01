/-
**標準形の項の算術: 和 `add`。**

段 1 の項の側の土台。`add x y` は順序数の和（x の y の先頭より小さい項を吸収）で、
標準形どうしの和は標準形、右の引数について狭義単調、左の引数について単調。
-/
import Ytosk.OTLemmas

namespace Ytosk

open T

theorem head_le_of_lt {x y : T} (h : x < y) : head x ≤ head y := by
  cases x with
  | z => simp [head, z_le]
  | psi a b c =>
    cases y with
    | z => exact absurd h (T.not_lt_z _)
    | psi d e f =>
      simp only [head]
      rw [T.psi_lt_psi] at h
      rw [le_iff, psi_lt_psi_z_iff]
      rcases h with h | ⟨rfl, h⟩ | ⟨rfl, rfl, _⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨rfl, h⟩)
      · exact Or.inr rfl

theorem head_le_self (x : T) : head x ≤ x := by
  cases x with
  | z => exact le_refl _
  | psi a b c =>
    simp only [head]
    cases c with
    | z => exact le_refl _
    | psi => exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, T.z_lt_psi _ _ _⟩))

@[simp] theorem add_z_left (y : T) : add z y = y := by cases y <;> rfl

@[simp] theorem add_z_right (x : T) : add x z = x := by cases x <;> rfl

theorem add_psi_psi (a b c d e f : T) :
    add (psi a b c) (psi d e f) =
      if psi a b z < psi d e z then psi d e f else psi a b (add c (psi d e f)) := by
  simp only [add, lt_iff_lt]

/-- The head of a sum. -/
theorem head_add_le {x y : T} (h : head y ≤ head x) (hx : x ≠ z) : head (add x y) = head x := by
  cases x with
  | z => exact absurd rfl hx
  | psi a b c =>
    cases y with
    | z => simp
    | psi d e f =>
      rw [add_psi_psi]
      have : ¬ psi a b z < psi d e z := not_lt_of_ge (by simpa [head] using h)
      simp [this, head]

/-- The sum of two standard terms is standard. -/
theorem isOT_add : ∀ {x y : T}, isOT x = true → isOT y = true → isOT (add x y) = true
  | z, _, _, hy => by simpa using hy
  | psi a b c, z, hx, _ => by simpa using hx
  | psi a b c, psi d e f, hx, hy => by
    rw [add_psi_psi]
    split
    · exact hy
    · rename_i hlt
      have hc : isOT (add c (psi d e f)) = true := isOT_add (isOT_rest hx) hy
      rw [isOT_psi_iff] at hx ⊢
      obtain ⟨h1, h2, _, h4, h5⟩ := hx
      refine ⟨h1, h2, hc, ?_, h5⟩
      by_cases hcz : c = z
      · subst hcz
        simp only [add_z_left, head]
        exact le_of_not_gt hlt
      · rcases le_total (head (psi d e f)) (head c) with h | h
        · rw [head_add_le h hcz]; exact h4
        · -- the head of `c` is absorbed or equal; the head of the sum is `head (psi d e f)` or `head c`
          have hhead : head (add c (psi d e f)) ≤ psi a b z := by
            cases c with
            | z => exact absurd rfl hcz
            | psi a' b' c' =>
              rw [add_psi_psi]
              split
              · simp only [head]; exact le_of_not_gt hlt
              · simpa [head] using h4
          exact hhead

/-- Right strict monotonicity of the sum. -/
theorem add_lt_add_left : ∀ (x : T) {y y' : T}, y < y' → add x y < add x y'
  | z, _, _, h => by simpa using h
  | psi a b c, y, y', h => by
    cases y' with
    | z => exact absurd h (T.not_lt_z _)
    | psi d' e' f' =>
      cases y with
      | z =>
        rw [add_z_right, add_psi_psi]
        split
        · rename_i hlt
          rw [T.psi_lt_psi]; rw [psi_lt_psi_z_iff] at hlt
          rcases hlt with hlt | ⟨rfl, hlt⟩
          · exact Or.inl hlt
          · exact Or.inr (Or.inl ⟨rfl, hlt⟩)
        · rw [T.psi_lt_psi]
          exact Or.inr (Or.inr ⟨rfl, rfl, by
            have := add_lt_add_left c (T.z_lt_psi d' e' f'); simpa using this⟩)
      | psi d e f =>
        have hhd : psi d e z ≤ psi d' e' z := by
          have := head_le_of_lt h; simpa [head] using this
        rw [add_psi_psi, add_psi_psi]
        by_cases h1 : psi a b z < psi d e z
        · have h2 : psi a b z < psi d' e' z := lt_of_lt_of_le h1 hhd
          simp only [h1, h2, if_true]; exact h
        · by_cases h2 : psi a b z < psi d' e' z
          · simp only [h1, h2, if_true, if_false]
            rw [T.psi_lt_psi]; rw [psi_lt_psi_z_iff] at h2
            rcases h2 with h2 | ⟨rfl, h2⟩
            · exact Or.inl h2
            · exact Or.inr (Or.inl ⟨rfl, h2⟩)
          · simp only [h1, h2, if_false]
            rw [T.psi_lt_psi]
            exact Or.inr (Or.inr ⟨rfl, rfl, add_lt_add_left c h⟩)

theorem add_le_add_left (x : T) {y y' : T} (h : y ≤ y') : add x y ≤ add x y' := by
  rcases (le_iff _ _).mp h with h | rfl
  · exact le_of_lt (add_lt_add_left x h)
  · exact le_refl _

/-- `y ≤ w + y` for a standard `y`. -/
theorem le_add_left_self {y : T} (hy : isOT y = true) : ∀ w : T, y ≤ add w y
  | z => by simp
  | psi a b c => by
    cases y with
    | z => exact z_le _
    | psi d e f =>
      rw [add_psi_psi]
      split
      · exact le_refl _
      · rename_i hlt
        have hle : psi d e z ≤ psi a b z := le_of_not_gt hlt
        rcases (le_iff _ _).mp hle with h | h
        · apply le_of_lt
          rw [T.psi_lt_psi]; rw [psi_lt_psi_z_iff] at h
          rcases h with h | ⟨rfl, h⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨rfl, h⟩)
        · simp only [psi.injEq, and_true] at h
          obtain ⟨rfl, rfl⟩ := h
          have ih : psi d e f ≤ add c (psi d e f) := le_add_left_self hy c
          have hf : f < psi d e f := rest_lt hy
          apply le_of_lt
          rw [T.psi_lt_psi]
          exact Or.inr (Or.inr ⟨rfl, rfl, lt_of_lt_of_le hf ih⟩)

/-- Left monotonicity of the sum. -/
theorem add_le_add_right : ∀ {x x' : T} (y : T), isOT x' = true → isOT y = true → x ≤ x' →
    add x y ≤ add x' y
  | x, z, y, _, _, h => by
    rcases (le_iff _ _).mp h with h | rfl
    · exact absurd h (T.not_lt_z _)
    · exact le_refl _
  | z, psi a' b' c', y, _, hy, _ => by simpa using le_add_left_self hy (psi a' b' c')
  | psi a b c, psi a' b' c', y, hx', hy, h => by
    cases y with
    | z => simpa using h
    | psi d e f =>
      rw [add_psi_psi, add_psi_psi]
      have hhd : psi a b z ≤ psi a' b' z := by
        have : head (psi a b c) ≤ head (psi a' b' c') := by
          rcases (le_iff _ _).mp h with h | h
          · exact head_le_of_lt h
          · rw [h]
        simpa [head] using this
      by_cases h2 : psi a' b' z < psi d e z
      · have h1 : psi a b z < psi d e z := lt_of_le_of_lt hhd h2
        simp [h1, h2]
      · by_cases h1 : psi a b z < psi d e z
        · simp only [h1, h2, if_true, if_false]
          have := le_add_left_self hy (psi a' b' c')
          rw [add_psi_psi] at this
          simpa [h2] using this
        · simp only [h1, h2, if_false]
          rcases (le_iff _ _).mp hhd with hlt | heq
          · apply le_of_lt
            rw [T.psi_lt_psi]; rw [psi_lt_psi_z_iff] at hlt
            rcases hlt with hlt | ⟨rfl, hlt⟩
            · exact Or.inl hlt
            · exact Or.inr (Or.inl ⟨rfl, hlt⟩)
          · simp only [psi.injEq, and_true] at heq
            obtain ⟨rfl, rfl⟩ := heq
            have hcc : c ≤ c' := by
              rcases (le_iff _ _).mp h with h | h
              · rw [T.psi_lt_psi] at h
                rcases h with h | ⟨_, h⟩ | ⟨_, _, h⟩
                · exact absurd h (lt_irrefl _)
                · exact absurd h (lt_irrefl _)
                · exact le_of_lt h
              · simp only [psi.injEq] at h; rw [h.2.2]
            have ih := add_le_add_right (psi d e f) (isOT_rest hx') hy hcc
            rcases (le_iff _ _).mp ih with ih | ih
            · apply le_of_lt; rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, ih⟩)
            · rw [ih]

end Ytosk
