/-
**3 行・t = 1: TrigOm の保存のための順序数の補題。**

D の値 ψ_s(y) は fsD で下がる。下がった値の引数 fsD(y, ζ) が Ω_{ν+1} の形なら、元の y も Ω_{t+1} の形
（`hole_om_shape`）。穴が対角点（DiagAt）なら fsD は Ω の形にならない（`diag_fsD_not_om`）。
穴が大きい共終数なら、fs(y, ζ) が Ω の形になるのは y = Ω_{t+1} のときだけ（`fs_om_shape`）。
ただし ζ が後続でない（ζ ≠ 1）ことが要る: ζ = 1 だと fs(Ω_1, 1) = 1 で、y = Ω_{Ω_1} から Ω_1 ができる。
-/
import Ytosk.V3FrameClN
import Ytosk.V3TP1

namespace Ytosk

open T

theorem isSucc_psi_z {a b : T} (h : a ≠ z ∨ b ≠ z) : isSucc (psi a b z) = false := by
  unfold isSucc last
  rcases h with h | h <;> simp [one, h]

theorem count_pos {η : T} (h : η ≠ z) : 0 < count η := by
  cases η with
  | z => exact absurd rfl h
  | psi _ _ _ => simp [count]

/-- `fs` of a term of big cofinality at a non-successor index is not a successor. -/
theorem fs_not_succ_big : ∀ {a μ η : T}, cof a = .big μ → η ≠ z → isSucc η = false →
    isSucc (fs a η) = false
  | z, _, _, h, _, _ => by simp [cof] at h
  | psi p q (psi c d e), μ, η, h, hη, hs => by
    have hc : cof (psi c d e) = .big μ := by simpa [cof] using h
    show isSucc (psi p q (fs (psi c d e) η)) = false
    rw [isSucc_psi_rest _ _ _ (fs_ne_z_big hc hη)]
    exact fs_not_succ_big hc hη hs
  | psi p q z, μ, η, h, hη, hs => by
    unfold fs
    unfold cof at h
    by_cases hq : q = z
    · subst hq
      rw [if_pos rfl] at h ⊢
      by_cases hp : p = z
      · rw [if_pos hp] at h; cases h
      · rw [if_neg hp] at h ⊢
        by_cases hps : isSucc p = true
        · rw [if_pos hps]; exact hs
        · rw [if_neg hps] at h ⊢
          exact isSucc_psi_z (Or.inl (fs_ne_z_big h hη))
    · rw [if_neg hq] at h ⊢
      by_cases hqs : isSucc q = true
      · rw [if_pos hqs] at h; cases h
      · rw [if_neg hqs] at h ⊢
        cases hcq : cof q with
        | big ν =>
          simp only
          split
          · exact isSucc_psi_z (Or.inr (fs_ne_z_big hcq hη))
          · apply isSucc_psi_z (Or.inr _)
            apply fs_ne_z_big hcq
            obtain ⟨k, hk⟩ : ∃ k, count η = k + 1 := ⟨count η - 1, by have := count_pos hη; omega⟩
            rw [hk]; simp
        | zero => rw [hcq] at h; cases h
        | succ => rw [hcq] at h; cases h
        | omega => rw [hcq] at h; cases h

/-- `fs(y, ζ)` (big cofinality) is `Ω_{ν+1}` only when `y` is some `Ω_{t+1}`. -/
theorem fs_om_shape : ∀ {y μ ζ ν : T}, cof y = .big μ → ζ ≠ z → isSucc ζ = false →
    fs y ζ = psi (succ ν) z z → ∃ t, y = psi (succ t) z z
  | z, _, _, _, h, _, _, _ => by simp [cof] at h
  | psi p q (psi c d e), μ, ζ, ν, h, hζ, _, he => by
    have hc : cof (psi c d e) = .big μ := by simpa [cof] using h
    have : fs (psi p q (psi c d e)) ζ = psi p q (fs (psi c d e) ζ) := rfl
    rw [this] at he
    exact absurd (T.psi.inj he).2.2 (fs_ne_z_big hc hζ)
  | psi p q z, μ, ζ, ν, h, hζ, hs, he => by
    unfold fs at he
    unfold cof at h
    by_cases hq : q = z
    · subst hq
      rw [if_pos rfl] at h he
      by_cases hp : p = z
      · rw [if_pos hp] at h; cases h
      · rw [if_neg hp] at h he
        by_cases hps : isSucc p = true
        · exact ⟨init p, by rw [show succ (init p) = p from init_app_one hps]⟩
        · rw [if_neg hps] at h he
          have h1 := (T.psi.inj he).1
          have h2 := fs_not_succ_big h hζ hs
          rw [h1, isSucc_succ] at h2; cases h2
    · rw [if_neg hq] at h he
      by_cases hqs : isSucc q = true
      · rw [if_pos hqs] at h; cases h
      · rw [if_neg hqs] at h he
        cases hcq : cof q with
        | big ν' =>
          rw [hcq] at he
          simp only at he
          split at he
          · exact absurd (T.psi.inj he).2.1 (fs_ne_z_big hcq hζ)
          · exfalso
            apply fs_ne_z_big hcq _ (T.psi.inj he).2.1
            obtain ⟨k, hk⟩ : ∃ k, count ζ = k + 1 := ⟨count ζ - 1, by have := count_pos hζ; omega⟩
            rw [hk]; simp
        | zero => rw [hcq] at h; cases h
        | succ => rw [hcq] at h; cases h
        | omega => rw [hcq] at h; cases h

/-- At a diagonal position, `fsD` is neither `Ω_{ν+1}` nor a successor. -/
theorem diag_fsD_not_om {a b μ ζ : T} (hζ : ζ ≠ z) {t : T} (hD : DiagAt a b μ t) :
    (∀ ν, fsD t ζ ≠ psi (succ ν) z z) ∧ isSucc (fsD t ζ) = false := by
  have hne : ∀ {t'}, DiagAt a b μ t' → fsD t' ζ ≠ z := fun h' =>
    fsD_ne_z_of_holeT (μ := μ) (br := b) (vr := a) hζ (Or.inr ⟨a, lt_irrefl' a, h'⟩)
  induction hD with
  | here hb hc _ =>
    rw [fsD_here hb hc]
    exact ⟨fun ν h => fs_ne_z_big hc hζ (T.psi.inj h).2.1, isSucc_psi_z (Or.inr (fs_ne_z_big hc hζ))⟩
  | @rest a' b' c d e h' ih =>
    have : fsD (psi a' b' (psi c d e)) ζ = psi a' b' (fsD (psi c d e) ζ) := rfl
    rw [this]
    exact ⟨fun ν h => hne h' (T.psi.inj h).2.2,
      by rw [isSucc_psi_rest _ _ _ (hne h')]; exact ih.2⟩
  | @arg a' b' hb hs h' _ =>
    rw [fsD_psi hb hs]
    exact ⟨fun ν h => hne h' (T.psi.inj h).2.1, isSucc_psi_z (Or.inr (hne h'))⟩
  | @sub a' ha hs h' ih =>
    rw [fsD_sub ha hs]
    refine ⟨fun ν h => ?_, isSucc_psi_z (Or.inl (hne h'))⟩
    have h1 := (T.psi.inj h).1
    have h2 := ih.2
    rw [h1, isSucc_succ] at h2; cases h2

/-- **The shape of a lowered value**: under a hole, if `fsD(ψ_s(y), ζ)` has the argument `Ω_{ν+1}`
(and `ζ` is not a successor), then `y` is some `Ω_{t+1}`. -/
theorem hole_om_shape {μ br vr s y ζ s' ν : T} (hH : HoleT μ br vr (psi s y z)) (hy : y ≠ z)
    (hζ : ζ ≠ z) (hζs : isSucc ζ = false)
    (h : fsD (psi s y z) ζ = psi s' (psi (succ ν) z z) z) : ∃ t, y = psi (succ t) z z := by
  rcases hH with hc | ⟨a', _, hD⟩
  · obtain ⟨hcy, _⟩ := cof_psi_inv hy hc
    rw [fsD_here hy hcy] at h
    exact fs_om_shape hcy hζ hζs (T.psi.inj h).2.1
  · cases hD with
    | here hb hc _ =>
      rw [fsD_here hb hc] at h
      exact fs_om_shape hc hζ hζs (T.psi.inj h).2.1
    | arg hb hs h' =>
      rw [fsD_psi hb hs] at h
      exact absurd (T.psi.inj h).2.1 ((diag_fsD_not_om hζ h').1 ν)
    | sub ha hs h' => exact absurd rfl hy

end Ytosk
