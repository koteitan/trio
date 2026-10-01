/-
**3 行: Ω 型の穴の fsD は ζ について単調（書き換えの持続の部品）。**

`OHole t`: fsD(t, ζ) の一番深い位置が Ω 型（ζ をそのまま入れる位置）。このとき
- fsD(t, ·) は（項の辞書式の順序で）単調（`fsD_mono_eta`）、
- ζ ≠ 0 なら fsD(t, ζ) ≠ 0（`fsD_ne_z_of_ohole`）。
したがって枠の不変条件「B < fsD(y, ψ_μ(1))」（TP1）か「B は y の先頭部分」（PRE）から、ψ_μ(1) ≤ ζ なら
B < fsD(y, ζ)（書き換えの持続 (W)）が出る（`persist_of_tp1`・`persist_of_pre`）。
-/
import Ytosk.V3FrameD

namespace Ytosk

open T

/-- The deepest position of `fsD` is of `Ω` type. -/
def OHole : T → Prop
  | z => False
  | psi _ _ (psi c d e) => OHole (psi c d e)
  | psi a b z =>
    if b = z then (a ≠ z ∧ (isSucc a = true ∨ OHole a))
    else if isSucc b then False
    else match cof b with
      | .big _ => True
      | _ => OHole b

theorem le_psi_rest {a b c c' : T} (h : c ≤ c') : psi a b c ≤ psi a b c' := by
  rcases (le_iff _ _).mp h with h | h
  · apply le_of_lt; rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, h⟩)
  · rw [h]

theorem le_psi_arg {a b b' : T} (h : b ≤ b') : psi a b z ≤ psi a b' z := by
  rcases (le_iff _ _).mp h with h | h
  · apply le_of_lt; rw [T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, h⟩)
  · rw [h]

theorem le_psi_sub {a a' : T} (h : a ≤ a') : psi a z z ≤ psi a' z z := by
  rcases (le_iff _ _).mp h with h | h
  · apply le_of_lt; rw [T.psi_lt_psi]; exact Or.inl h
  · rw [h]

/-- **`fsD` is monotone in the index at an `Ω`-type hole.** -/
theorem fsD_mono_eta : ∀ {t η η' : T}, OHole t → η ≤ η' → fsD t η ≤ fsD t η'
  | z, _, _, h, _ => by simp [OHole] at h
  | psi a b (psi c d e), η, η', h, hle => by
    have h' : OHole (psi c d e) := h
    show psi a b (fsD (psi c d e) η) ≤ psi a b (fsD (psi c d e) η')
    exact le_psi_rest (fsD_mono_eta h' hle)
  | psi a b z, η, η', h, hle => by
    unfold OHole at h
    unfold fsD
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl] at h
      simp only [if_pos rfl]
      obtain ⟨ha, h⟩ := h
      simp only [if_neg ha]
      by_cases hs : isSucc a = true
      · simp only [if_pos hs]; exact hle
      · simp only [if_neg hs]
        have ha' : OHole a := by rcases h with h | h; exact absurd h hs; exact h
        exact le_psi_sub (fsD_mono_eta ha' hle)
    · rw [if_neg hb] at h
      simp only [if_neg hb]
      by_cases hs : isSucc b = true
      · rw [if_pos hs] at h; exact absurd h id
      · rw [if_neg hs] at h
        simp only [if_neg hs]
        cases hcb : cof b with
        | big μ =>
          simp only
          rcases (le_iff _ _).mp hle with hlt | heq
          · exact le_psi_arg (le_of_lt (fs_mono hcb hlt))
          · rw [heq]
        | zero =>
          rw [hcb] at h; simp only at h ⊢
          exact le_psi_arg (fsD_mono_eta h hle)
        | succ =>
          rw [hcb] at h; simp only at h ⊢
          exact le_psi_arg (fsD_mono_eta h hle)
        | omega =>
          rw [hcb] at h; simp only at h ⊢
          exact le_psi_arg (fsD_mono_eta h hle)

/-- **Persistence from TP1.** -/
theorem persist_of_tp1 {b y η₀ ζ : T} (hy : OHole y) (h0 : η₀ ≤ ζ) (h : b < fsD y η₀) :
    lt b (fsD y ζ) = true :=
  lt_of_lt_of_le h (fsD_mono_eta hy h0)

end Ytosk
