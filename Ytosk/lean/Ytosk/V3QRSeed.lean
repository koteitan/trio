/-
**3 行・t = 1・q = r: 始点 seed = o_{M[1]}(r) の条件。**

- `spArg_seed`: seed < A = ψ_μ(b + Ω_{μ+1}) なら spArg(μ, b, seed) = b + seed（書き換えが起きるのは添字 μ で
  b < σ < b + Ω_{μ+1} のときだけで、σ の高い部分は b、低い部分は 0 でない）。
- 落とす補題から seed ◁ A（`qr_seed_lhd`）。添字 μ なら SeedOK は `seedOK_of_lhd_top`、
  添字が μ より小さいなら成分の条件（仮定）から `seedOK_of_c2`。
-/
import Ytosk.V3QRFinal2

namespace Ytosk

open T

/-- **Above `b` among all-high terms means at least `b + θ`.** -/
theorem le_app_of_gt_hi {θ : T} (hθ : ∃ m, θ = psi m z z) :
    ∀ {b H : T}, (∀ q ∈ summands H, ¬ q < θ) → b < H → app b θ ≤ H
  | z, H, hH, hbH => by
    show θ ≤ H
    cases H with
    | z => exact absurd hbH (T.not_lt_z _)
    | psi a c d =>
      have h1 : ¬ psi a c z < θ := hH _ (by simp [summands])
      exact le_trans (le_of_not_gt h1) (head_le_self (psi a c d))
  | psi a c d, H, hH, hbH => by
    cases H with
    | z => exact absurd hbH (T.not_lt_z _)
    | psi a' c' d' =>
      rw [app_psi]
      rw [T.psi_lt_psi] at hbH
      rcases hbH with h | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩
      · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inl h)
      · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, h⟩))
      · have hH' : ∀ q ∈ summands d', ¬ q < θ := fun q hq => hH q (by simp [summands, hq])
        have ih := le_app_of_gt_hi hθ hH' h
        rcases (le_iff _ _).mp ih with h' | h'
        · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, h'⟩))
        · rw [h']

/-- **The frame at `r` with the seed**: `spArg(μ, b, seed) = b + seed` for a seed below `A`. -/
theorem spArg_seed {μ b s σ : T} (hb : AllGeT (psi (succ μ) z z) b) (hot : isOT (psi s σ z) = true)
    (hlt : psi s σ z < psi μ (app b (psi (succ μ) z z)) z) :
    spArg μ b (psi s σ z) = app b (psi s σ z) := by
  have hΩ : psi μ (app b (psi (succ μ) z z)) z < psi (succ μ) z z := by
    rw [psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self μ)
  have hsΩ : psi s σ z < psi (succ μ) z z := lt_trans hlt hΩ
  rw [spArg_cons]; show step μ b s σ z = _
  unfold step
  by_cases htr : lt b σ = true ∧ lt (psi μ z z) (psi s σ z) = true
  · rw [if_pos htr, H_eq hot]
    -- the subscript is `μ`
    have hsμ : s = μ := by
      have h1 : psi μ z z < psi s σ z := htr.2
      rw [psi_lt_psi_z_iff] at h1 hlt
      rcases hlt with h | ⟨h, _⟩
      · rcases h1 with h' | ⟨h', _⟩
        · exact absurd (lt_trans h h') (lt_irrefl' _)
        · rw [h'] at h; exact absurd h (lt_irrefl' _)
      · exact h
    subst hsμ
    have hσlt : σ < app b (psi (succ s) z z) := by
      rw [psi_lt_psi_z_iff] at hlt
      rcases hlt with h | ⟨_, h⟩
      · exact absurd h (lt_irrefl' _)
      · exact h
    -- split at `Ω_{s+1}`: the high part is `b`, the low part is nonzero
    have hall : ∀ q ∈ summands (app b (psi (succ s) z z)), ¬ q < psi (succ s) z z := by
      intro q hq
      rw [summands_app] at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hb q hq
      · simp [summands] at hq; rw [hq]; exact lt_irrefl' _
    have hsB : split (app b (psi (succ s) z z)) (psi (succ s) z z) = (app b (psi (succ s) z z), z) := by
      have := split_app_of (B := app b (psi (succ s) z z)) (X := z) hall (Or.inl rfl)
      rwa [app_z_right] at this
    have hsb : split b (psi (succ s) z z) = (b, z) := by
      have := split_app_of (B := b) (X := z) hb (Or.inl rfl)
      rwa [app_z_right] at this
    have hhi_lt : (split σ (psi (succ s) z z)).1 < app b (psi (succ s) z z) := by
      rcases split_mono (psi (succ s) z z) hσlt with h | ⟨_, h⟩
      · rw [hsB] at h; exact h
      · rw [hsB] at h; exact absurd h (T.not_lt_z _)
    have hhi_high : ∀ q ∈ summands (split σ (psi (succ s) z z)).1, ¬ q < psi (succ s) z z :=
      split_fst_ge _ σ
    rcases split_mono (psi (succ s) z z) (show b < σ from htr.1) with h | ⟨h, h'⟩
    · rw [hsb] at h
      exact absurd (lt_of_le_of_lt (le_app_of_gt_hi ⟨succ s, rfl⟩ hhi_high h) hhi_lt) (lt_irrefl' _)
    · rw [hsb] at h h'
      have hlo : (split σ (psi (succ s) z z)).2 ≠ z := by
        intro he; rw [he] at h'; exact T.not_lt_z _ h'
      rw [← h, if_neg hlo]
  · rw [if_neg htr]
    apply add_eq_app_of_ge ⟨s, σ, rfl⟩ b
    intro q hq
    exact le_of_lt (lt_of_lt_of_le hsΩ (le_of_not_gt (hb q hq)))

end Ytosk
