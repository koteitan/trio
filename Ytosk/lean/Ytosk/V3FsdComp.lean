/-
**fsD の合成: 穴に ζ を入れてから θ を入れるのは、ζ[θ] を入れるのと同じ。**

`fsD (fsD t ζ) θ = fsD t (fsD ζ θ)`（t に穴があり、ζ が 0 でも後続でもないとき、`fsD_comp`）。
穴が Ω_{μ+1} 型（cof t = Ω_{μ+1}）でも対角点（`DiagAt`）でも、fsD は穴の位置に ζ を置くだけなので、
次の fsD は ζ の中の穴に進む。Ω_{μ+1} 型の部分は `fs` で置き換わる（`fsD_fs_comp`）。
-/
import Ytosk.V3TP1

namespace Ytosk

open T

set_option linter.unusedSectionVars false

theorem isSucc_psi_ne {a b : T} (h : a ≠ z ∨ b ≠ z) : isSucc (psi a b z) = false := by
  unfold isSucc last
  rcases h with h | h <;> simp [one, h]

/-- `fs` of an `Ω_{μ+1}`-cofinal term at a nonzero non-successor index is not a successor. -/
theorem isSucc_fs_big : ∀ {b μ ζ : T}, cof b = .big μ → ζ ≠ z → isSucc ζ = false →
    isSucc (fs b ζ) = false
  | z, _, _, h, _, _ => by simp [cof] at h
  | psi a b (psi c d e), μ, ζ, h, hζ, hs => by
    have h' : cof (psi c d e) = .big μ := by simpa [cof] using h
    show isSucc (psi a b (fs (psi c d e) ζ)) = false
    rw [isSucc_psi_rest _ _ _ (fs_ne_z_big h' hζ)]
    exact isSucc_fs_big h' hζ hs
  | psi a b z, μ, ζ, h, hζ, hs => by
    unfold cof at h
    unfold fs
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl] at h ⊢
      by_cases ha : a = z
      · rw [if_pos ha] at h; cases h
      · rw [if_neg ha] at h ⊢
        by_cases has : isSucc a = true
        · rw [if_pos has]; exact hs
        · rw [if_neg has] at h ⊢
          exact isSucc_psi_ne (Or.inl (fs_ne_z_big h hζ))
    · rw [if_neg hb] at h ⊢
      by_cases hbs : isSucc b = true
      · rw [if_pos hbs] at h; cases h
      · rw [if_neg hbs] at h ⊢
        cases hcb : cof b with
        | big ν =>
          rw [hcb] at h; simp only at h ⊢
          by_cases hν : lt ν a = true
          · rw [if_pos hν]; exact isSucc_psi_ne (Or.inr (fs_ne_z_big hcb hζ))
          · rw [if_neg hν] at h; cases h
        | zero => rw [hcb] at h; cases h
        | succ => rw [hcb] at h; cases h
        | omega => rw [hcb] at h; cases h

/-- **`fsD` at a hole is nonzero** (for a nonzero index). -/
theorem fsD_ne_z_oh : ∀ {t ζ : T}, OHole t → ζ ≠ z → fsD t ζ ≠ z
  | z, _, h, _ => by simp [OHole] at h
  | psi a b (psi c d e), _, _, _ => by simp [fsD]
  | psi a b z, ζ, h, hζ => by
    unfold OHole at h
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl] at h
      obtain ⟨ha, _⟩ := h
      by_cases has : isSucc a = true
      · rw [fsD_leaf has ha]; exact hζ
      · rw [fsD_sub ha (by simpa using has)]; simp
    · rw [if_neg hb] at h
      by_cases hbs : isSucc b = true
      · rw [if_pos hbs] at h; exact absurd h id
      · rw [fsD_psi hb (by simpa using hbs)]; simp

/-- **`fsD` at a hole is not a successor** (for a nonzero non-successor index). -/
theorem isSucc_fsD_oh : ∀ {t ζ : T}, OHole t → ζ ≠ z → isSucc ζ = false → isSucc (fsD t ζ) = false
  | z, _, h, _, _ => by simp [OHole] at h
  | psi a b (psi c d e), ζ, h, hζ, hs => by
    have h' : OHole (psi c d e) := h
    show isSucc (psi a b (fsD (psi c d e) ζ)) = false
    rw [isSucc_psi_rest _ _ _ (fsD_ne_z_oh h' hζ)]
    exact isSucc_fsD_oh h' hζ hs
  | psi a b z, ζ, h, hζ, hs => by
    unfold OHole at h
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl] at h
      obtain ⟨ha, h⟩ := h
      by_cases has : isSucc a = true
      · rw [fsD_leaf has ha]; exact hs
      · rw [fsD_sub ha (by simpa using has)]
        have ha' : OHole a := by rcases h with h | h; exact absurd h has; exact h
        exact isSucc_psi_ne (Or.inl (fsD_ne_z_oh ha' hζ))
    · rw [if_neg hb] at h
      by_cases hbs : isSucc b = true
      · rw [if_pos hbs] at h; exact absurd h id
      · rw [fsD_psi hb (by simpa using hbs)]
        rw [if_neg (by simpa using hbs)] at h
        apply isSucc_psi_ne (Or.inr ?_)
        cases hcb : cof b with
        | big ν => rw [fsD_eq_fs hcb]; exact fs_ne_z_big hcb hζ
        | zero => rw [hcb] at h; exact fsD_ne_z_oh h hζ
        | succ => rw [hcb] at h; exact fsD_ne_z_oh h hζ
        | omega => rw [hcb] at h; exact fsD_ne_z_oh h hζ

theorem fsD_rest {a b X : T} (hX : X ≠ z) (θ : T) : fsD (psi a b X) θ = psi a b (fsD X θ) := by
  cases X with
  | z => exact absurd rfl hX
  | psi => rfl

theorem fs_rest {a b X : T} (hX : X ≠ z) (θ : T) : fs (psi a b X) θ = psi a b (fs X θ) := by
  cases X with
  | z => exact absurd rfl hX
  | psi => rfl

theorem fs_leaf' {a : T} (ha : a ≠ z) (hs : isSucc a = true) (η : T) : fs (psi a z z) η = η := by
  unfold fs; rw [if_pos rfl, if_neg ha, if_pos hs]

theorem fs_sub' {a : T} (ha : a ≠ z) (hs : isSucc a = false) (η : T) :
    fs (psi a z z) η = psi (fs a η) z z := by
  conv => lhs; unfold fs
  rw [if_pos rfl, if_neg ha, if_neg (by rw [hs]; simp)]

theorem fs_big' {a b ν : T} (hb : b ≠ z) (hs : isSucc b = false) (hc : cof b = .big ν)
    (hν : lt ν a = true) (η : T) : fs (psi a b z) η = psi a (fs b η) z := by
  conv => lhs; unfold fs
  rw [if_neg hb, if_neg (by rw [hs]; simp), hc]
  simp only
  rw [if_pos hν]

/-- **Composition at an `Ω_{μ+1}`-cofinal term**: `fs b ζ` then `fsD · θ` is `fs b (fsD ζ θ)`. -/
theorem fsD_fs_comp : ∀ {b μ ζ : T}, cof b = .big μ → ζ ≠ z → isSucc ζ = false → ∀ θ,
    fsD (fs b ζ) θ = fs b (fsD ζ θ)
  | z, _, _, h, _, _, _ => by simp [cof] at h
  | psi a b (psi c d e), μ, ζ, h, hζ, hs, θ => by
    have h' : cof (psi c d e) = .big μ := by simpa [cof] using h
    show fsD (psi a b (fs (psi c d e) ζ)) θ = psi a b (fs (psi c d e) (fsD ζ θ))
    rw [fsD_rest (fs_ne_z_big h' hζ), fsD_fs_comp h' hζ hs θ]
  | psi a b z, μ, ζ, h, hζ, hs, θ => by
    have hc := h
    unfold cof at h
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl] at h
      by_cases ha : a = z
      · rw [if_pos ha] at h; cases h
      · rw [if_neg ha] at h
        by_cases has : isSucc a = true
        · rw [fs_leaf' ha has, fs_leaf' ha has]
        · rw [if_neg has] at h
          have has' : isSucc a = false := by simpa using has
          rw [fs_sub' ha has', fs_sub' ha has', fsD_sub (fs_ne_z_big h hζ) (isSucc_fs_big h hζ hs),
            fsD_fs_comp h hζ hs θ]
    · rw [if_neg hb] at h
      by_cases hbs : isSucc b = true
      · rw [if_pos hbs] at h; cases h
      · rw [if_neg hbs] at h
        have hbs' : isSucc b = false := by simpa using hbs
        cases hcb : cof b with
        | big ν =>
          rw [hcb] at h; simp only at h
          by_cases hν : lt ν a = true
          · rw [fs_big' hb hbs' hcb hν, fs_big' hb hbs' hcb hν,
              fsD_psi (fs_ne_z_big hcb hζ) (isSucc_fs_big hcb hζ hs), fsD_fs_comp hcb hζ hs θ]
          · rw [if_neg hν] at h; cases h
        | zero => rw [hcb] at h; cases h
        | succ => rw [hcb] at h; cases h
        | omega => rw [hcb] at h; cases h

/-- **Composition of `fsD` at a hole**: `fsD (fsD t ζ) θ = fsD t (fsD ζ θ)`. -/
theorem fsD_comp : ∀ {t ζ : T}, OHole t → ζ ≠ z → isSucc ζ = false → ∀ θ,
    fsD (fsD t ζ) θ = fsD t (fsD ζ θ)
  | z, _, h, _, _, _ => by simp [OHole] at h
  | psi a b (psi c d e), ζ, h, hζ, hs, θ => by
    have h' : OHole (psi c d e) := h
    show fsD (psi a b (fsD (psi c d e) ζ)) θ = psi a b (fsD (psi c d e) (fsD ζ θ))
    rw [fsD_rest (fsD_ne_z_oh h' hζ), fsD_comp h' hζ hs θ]
  | psi a b z, ζ, h, hζ, hs, θ => by
    unfold OHole at h
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl] at h
      obtain ⟨ha, h⟩ := h
      by_cases has : isSucc a = true
      · rw [fsD_leaf has ha, fsD_leaf has ha]
      · have has' : isSucc a = false := by simpa using has
        have ha' : OHole a := by rcases h with h | h; exact absurd h has; exact h
        rw [fsD_sub ha has', fsD_sub ha has',
          fsD_sub (fsD_ne_z_oh ha' hζ) (isSucc_fsD_oh ha' hζ hs), fsD_comp ha' hζ hs θ]
    · rw [if_neg hb] at h
      by_cases hbs : isSucc b = true
      · rw [if_pos hbs] at h; exact absurd h id
      · rw [if_neg hbs] at h
        have hbs' : isSucc b = false := by simpa using hbs
        rw [fsD_psi hb hbs', fsD_psi hb hbs']
        cases hcb : cof b with
        | big ν =>
          rw [fsD_eq_fs hcb, fsD_eq_fs hcb,
            fsD_psi (fs_ne_z_big hcb hζ) (isSucc_fs_big hcb hζ hs), fsD_fs_comp hcb hζ hs θ]
        | zero =>
          rw [hcb] at h
          rw [fsD_psi (fsD_ne_z_oh h hζ) (isSucc_fsD_oh h hζ hs), fsD_comp h hζ hs θ]
        | succ =>
          rw [hcb] at h
          rw [fsD_psi (fsD_ne_z_oh h hζ) (isSucc_fsD_oh h hζ hs), fsD_comp h hζ hs θ]
        | omega =>
          rw [hcb] at h
          rw [fsD_psi (fsD_ne_z_oh h hζ) (isSucc_fsD_oh h hζ hs), fsD_comp h hζ hs θ]

end Ytosk
