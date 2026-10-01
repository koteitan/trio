/-
**落とす補題: 枠の 1 段（step）で DomLe が伝わる。**

落とした値の子 ψ_{s'}(y') と基準の子 ψ_ŝ(ŷ)（γ_k を入れた値）の間に DomLe があるとき、
同じ前の状態 B・同じ親の添字 a の 1 段 step も DomLe で並ぶ（実測で書き換えの有無は両側で一致）。
- 書き換えなし同士（`domle_step_nn`）: B の項で ψ_ŝ(ŷ) に吸収されるものは ψ_{s'}(y') にも吸収される、が条件。
- 書き換えあり同士（`domle_step_tt`）: 添字が同じで、y' の低い部分があれば ŷ にもある。
-/
import Ytosk.V3DomLe

namespace Ytosk

open T

/-- Weakening the target of `DomLe`. -/
theorem domle_weaken {μ t a b : T} (h : DomLe μ t a) (htb : t ≤ b)
    (ha : ∀ u, ¬ lt μ u = true → a ≤ b ∨ ∃ y ∈ comps u b, a ≤ y)
    (hab : ∀ u, ¬ lt μ u = true → ∀ g ∈ comps u a, g ≤ b ∨ ∃ y ∈ comps u b, g ≤ y) :
    DomLe μ t b := by
  refine ⟨htb, ?_⟩
  intro u hu g hg
  rcases h.2 u hu g hg with h1 | ⟨w, hw, hgw⟩
  · rcases ha u hu with h2 | ⟨y, hy, hay⟩
    · exact Or.inl (le_trans h1 h2)
    · exact Or.inr ⟨y, hy, le_trans h1 hay⟩
  · rcases hab u hu w hw with h2 | ⟨y, hy, hwy⟩
    · exact Or.inl (le_trans hgw h2)
    · exact Or.inr ⟨y, hy, le_trans hgw hwy⟩

/-- A prefix is below. -/
theorem domle_prefix (μ P X : T) : DomLe μ P (app P X) := by
  refine ⟨le_app_self P X, ?_⟩
  intro u _ g hg
  exact Or.inr ⟨g, by rw [comps_app]; exact List.mem_append_left _ hg, le_refl g⟩

/-- **No rewrite on either side.** -/
theorem domle_step_nn {μ a B s' y' s y : T} (hBot : isOT B = true) (hc : isOT (psi s y z) = true)
    (hX : DomLe μ (psi s' y' z) (psi s y z))
    (hn' : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true))
    (hn : ¬ (lt B y = true ∧ lt (psi a z z) (psi s y z) = true))
    (hBm : ∀ q ∈ summands B, q < psi s y z → q < psi s' y' z) :
    DomLe μ (step a B s' y' z) (step a B s y z) := by
  unfold step
  rw [if_neg hn', if_neg hn]
  obtain ⟨P, Q, hB, hQ, hadd⟩ := add_prefix s y B
  have hPge : ∀ q ∈ summands P, ¬ q < psi s y z := by
    intro q hq hlt
    have : q ∈ summands (add B (psi s y z)) := by
      rw [hadd, summands_app]; exact List.mem_append_left _ hq
    exact lt_irrefl' _ (lt_of_le_of_lt (add_summands_ge B q this) hlt)
  have hadd' : add B (psi s' y' z) = app P (psi s' y' z) := by
    rw [hB]
    apply add_app_drop
    · intro q hq hlt; exact hPge q hq (lt_of_lt_of_le hlt hX.1)
    · cases hQc : Q with
      | z => exact Or.inl rfl
      | psi q1 q2 q3 =>
        right
        apply hBm
        · rw [hB, summands_app, hQc]; apply List.mem_append_right; simp [summands, head]
        · have := lt_of_le_of_lt (head_le_self Q) hQ
          rw [hQc] at this; simpa [head] using this
  rw [hadd', hadd]
  apply domle_app hX
  rw [← hadd]; exact isOT_add hBot hc

/-- **A rewrite on both sides** (same subscript). -/
theorem domle_step_tt {μ a B s y' y : T} (hc' : isOT (psi s y' z) = true)
    (hc : isOT (psi s y z) = true) (hsμ : lt μ s = true)
    (hot : isOT (step a B s y z) = true)
    (ht' : lt B y' = true ∧ lt (psi a z z) (psi s y' z) = true)
    (ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hy : DomLe μ y' y)
    (hlo : (split y' (psi (succ s) z z)).2 ≠ z → (split y (psi (succ s) z z)).2 ≠ z)
    (hhi : (split y' (psi (succ s) z z)).2 ≠ z →
      (split y' (psi (succ s) z z)).1 = (split y (psi (succ s) z z)).1) :
    DomLe μ (step a B s y' z) (step a B s y z) := by
  unfold step at hot ⊢
  rw [if_pos ht'] at ⊢
  rw [if_pos ht] at hot ⊢
  rw [H_eq hc', H_eq hc]
  rw [H_eq hc] at hot
  have hsu : ∀ u, ¬ lt μ u = true → ¬ lt s u = true := fun u hu h => hu (show μ < u from lt_trans (show μ < s from hsμ) (show s < u from h))
  have hspl := fun t : T => split_app (psi (succ s) z z) t
  by_cases hl : (split y (psi (succ s) z z)).2 = z
  · have hl' : (split y' (psi (succ s) z z)).2 = z := by
      by_contra h; exact hlo h hl
    rw [if_pos hl, if_pos hl', app_z_right, app_z_right]
    have e1 := hspl y; rw [hl, app_z_right] at e1
    have e2 := hspl y'; rw [hl', app_z_right] at e2
    rw [e1, e2]; exact hy
  · rw [if_neg hl]
    rw [if_neg hl] at hot
    by_cases hl' : (split y' (psi (succ s) z z)).2 = z
    · rw [if_pos hl', app_z_right]
      have e2 := hspl y'; rw [hl', app_z_right] at e2
      rw [e2]
      -- `y' ≤ y ≤ H s y`, and `y` and its components are components of `ψ_s(y)`
      have hyH : y ≤ app (split y (psi (succ s) z z)).1 (psi s y z) := by
        have := le_H hc; rw [H_eq hc, if_neg hl] at this; exact this
      apply domle_weaken hy (le_trans hy.1 hyH)
      · intro u hu
        right
        refine ⟨y, ?_, le_refl y⟩
        rw [comps_app]; apply List.mem_append_right
        simp [comps, hsu u hu]
      · intro u hu g hg
        right
        refine ⟨g, ?_, le_refl g⟩
        rw [comps_app]; apply List.mem_append_right
        exact mem_comps_psi_arg (hsu u hu) hg
    · rw [if_neg hl', hhi hl']
      exact domle_app (domle_psi hy) hot

end Ytosk
