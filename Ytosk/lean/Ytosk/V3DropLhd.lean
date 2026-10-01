/-
**落とす補題: Lhd 版の枠 1 段**（落とした値の標準形のため）。

`LhdE b a`: b = a か b ◁ a（`Lhd z`）。落とした値 v′ と基準（r の部分木では F_{k+1}、r とその下では M の値）の間に
成り立つ（実測）。ψ_a(基準) が標準形なら ψ_a(v′) も標準形（`psi_ot_of_lhd`）。
-/
import Ytosk.V3DropStep

namespace Ytosk

open T

/-- Equal or below in Buchholz's sense (index `0`). -/
def LhdE (b a : T) : Prop := b = a ∨ Lhd z b a

theorem LhdE.le {b a : T} (h : LhdE b a) : b ≤ a := by
  rcases h with rfl | h
  · exact le_refl _
  · exact le_of_lt h.1

theorem LhdE.trans {a b c : T} (h1 : LhdE a b) (h2 : LhdE b c) : LhdE a c := by
  rcases h1 with rfl | h1
  · exact h2
  · rcases h2 with rfl | h2
    · exact Or.inr h1
    · exact Or.inr (lhd_trans h1 h2)

theorem lhdE_app {b0 b : T} (A : T) (h : LhdE b0 b) : LhdE (app A b0) (app A b) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (lhd_app A h)

theorem lhdE_psi {b0 b : T} (v : T) (h : LhdE b0 b) : LhdE (psi v b0 z) (psi v b z) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (lhd_psi v h)

theorem lhdE_prefix (A C : T) : LhdE A (app A C) := by
  by_cases hC : C = z
  · subst hC; left; simp
  · exact Or.inr (lhd_prefix hC)

/-- **No rewrite on either side** (Lhd version). -/
theorem lhdE_step_nn {a B s' y' s y : T} (hX : LhdE (psi s' y' z) (psi s y z))
    (hn' : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true))
    (hn : ¬ (lt B y = true ∧ lt (psi a z z) (psi s y z) = true))
    (hBm : ∀ q ∈ summands B, q < psi s y z → q < psi s' y' z) :
    LhdE (step a B s' y' z) (step a B s y z) := by
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
    · intro q hq hlt; exact hPge q hq (lt_of_lt_of_le hlt hX.le)
    · cases hQc : Q with
      | z => exact Or.inl rfl
      | psi q1 q2 q3 =>
        right
        apply hBm
        · rw [hB, summands_app, hQc]; apply List.mem_append_right; simp [summands, head]
        · have := lt_of_le_of_lt (head_le_self Q) hQ
          rw [hQc] at this; simpa [head] using this
  rw [hadd', hadd]
  exact lhdE_app P hX

/-- **A rewrite on both sides** (Lhd version, same subscript). -/
theorem lhdE_step_tt {a B s y' y : T} (hc' : isOT (psi s y' z) = true)
    (hc : isOT (psi s y z) = true)
    (ht' : lt B y' = true ∧ lt (psi a z z) (psi s y' z) = true)
    (ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hy : LhdE y' y)
    (hlo : (split y' (psi (succ s) z z)).2 ≠ z → (split y (psi (succ s) z z)).2 ≠ z)
    (hhi : (split y' (psi (succ s) z z)).2 ≠ z →
      (split y' (psi (succ s) z z)).1 = (split y (psi (succ s) z z)).1)
    (hmis : (split y' (psi (succ s) z z)).2 = z → (split y (psi (succ s) z z)).2 ≠ z →
      LhdE y' (app (split y (psi (succ s) z z)).1 (psi s y z))) :
    LhdE (step a B s y' z) (step a B s y z) := by
  unfold step
  rw [if_pos ht', if_pos ht, H_eq hc', H_eq hc]
  have hspl := fun t : T => split_app (psi (succ s) z z) t
  by_cases hl : (split y (psi (succ s) z z)).2 = z
  · have hl' : (split y' (psi (succ s) z z)).2 = z := by
      by_contra h; exact hlo h hl
    rw [if_pos hl, if_pos hl', app_z_right, app_z_right]
    have e1 := hspl y; rw [hl, app_z_right] at e1
    have e2 := hspl y'; rw [hl', app_z_right] at e2
    rw [e1, e2]; exact hy
  · rw [if_neg hl]
    by_cases hl' : (split y' (psi (succ s) z z)).2 = z
    · rw [if_pos hl', app_z_right]
      have e2 := hspl y'; rw [hl', app_z_right] at e2
      rw [e2]; exact hmis hl' hl
    · rw [if_neg hl', hhi hl']
      exact lhdE_app _ (lhdE_psi s hy)

/-- **`ψ_v` of a smaller argument whose components are at most itself** is below. -/
theorem lhd_psi_small {η b0 b : T} (v : T) (hlt : b0 < b)
    (hsm : ∀ u, ¬ lt v u = true → ∀ g ∈ comps u b0, g ≤ b0) : Lhd η (psi v b0 z) (psi v b z) := by
  refine ⟨by rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, hlt⟩, fun u c h1 h2 => ?_⟩
  obtain ⟨c0, c1, rfl, hc1, hc2⟩ := between_psi h1 h2
  intro x hx
  simp only [comps, List.mem_append] at hx
  rcases hx with hx | hx
  · split at hx
    · simp at hx
    · rename_i hvu
      have hc0 : c0 ∈ comps u (psi v c0 c1) := by simp [comps, hvu]
      simp only [List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | hx
      · exact ⟨c0, List.mem_append_left _ hc0, hc1⟩
      · exact ⟨c0, List.mem_append_left _ hc0, le_trans (hsm u hvu x hx) hc1⟩
      · exact ⟨x, List.mem_append_left _ (by simp [comps, hvu, hx]), le_refl _⟩
  · simp [comps] at hx

theorem lhdE_psi_small {b0 b : T} (v : T) (hle : b0 ≤ b)
    (hsm : ∀ u, ¬ lt v u = true → ∀ g ∈ comps u b0, g ≤ b0) : LhdE (psi v b0 z) (psi v b z) := by
  rcases (le_iff _ _).mp hle with h | h
  · exact Or.inr (lhd_psi_small v h hsm)
  · left; rw [h]

/-- **No rewrite on either side, with the state above the child** (`hBm` is then vacuous). -/
theorem lhdE_step_nn' {a B s' y' s y : T} (hX : LhdE (psi s' y' z) (psi s y z))
    (hn' : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true))
    (hn : ¬ (lt B y = true ∧ lt (psi a z z) (psi s y z) = true))
    (hB : ∀ q ∈ summands B, psi s y z ≤ q) :
    LhdE (step a B s' y' z) (step a B s y z) :=
  lhdE_step_nn hX hn' hn (fun q hq hlt => absurd (lt_of_le_of_lt (hB q hq) hlt) (lt_irrefl' _))

/-- Restricting the interval of `◁`. -/
theorem lhd_restrict {η b a a' : T} (h : Lhd η b a) (h1 : b < a') (h2 : a' ≤ a) : Lhd η b a' :=
  ⟨h1, fun u c hc1 hc2 => h.2 u c hc1 (le_trans hc2 h2)⟩

/-- A term with no low part that is below `y` is at most the high part of `y`. -/
theorem le_hi_of_nolo {θ y' y : T} (hot : isOT y = true) (hle : y' ≤ y)
    (hl' : (split y' θ).2 = z) : y' ≤ (split y θ).1 := by
  have e := split_app θ y'
  rw [hl', app_z_right] at e
  rcases (le_iff _ _).mp hle with hlt | heq
  · rcases split_mono θ hlt with h | ⟨h, _⟩
    · rw [← e]; exact le_of_lt h
    · rw [← e, h]
  · rw [← e, heq]

/-- **`hmis` from the argument relation**: if `y'` has no low part and `y` has one, then
`y' ◁ hi(y) + ψ_s(y)`. -/
theorem hmis_of_lhdE {s y' y : T} (hot : isOT y = true) (hy : LhdE y' y)
    (hl' : (split y' (psi (succ s) z z)).2 = z) :
    LhdE y' (app (split y (psi (succ s) z z)).1 (psi s y z)) := by
  have hle := le_hi_of_nolo hot hy.le hl'
  apply LhdE.trans (b := (split y (psi (succ s) z z)).1) _ (lhdE_prefix _ _)
  rcases (le_iff _ _).mp hle with hlt | heq
  · rcases hy with rfl | hy
    · -- `y' = y` has no low part, so `y = hi(y)`
      have e := split_app (psi (succ s) z z) y'
      rw [hl', app_z_right] at e
      rw [e] at hlt; exact absurd hlt (lt_irrefl' _)
    · exact Or.inr (lhd_restrict hy hlt (by
        have := le_app_self (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2
        rw [split_app] at this; exact this))
  · exact Or.inl heq

/-- Splitting `P ++ R` when the head of `R` is low. -/
theorem split_app_low {θ : T} : ∀ {P R : T}, (R = z ∨ head R < θ) →
    split (app P R) θ = ((split P θ).1, app (split P θ).2 R)
  | z, R, hR => by
    rcases hR with rfl | hR
    · rfl
    · cases R with
      | z => rfl
      | psi a b c =>
        simp only [app_z, split]
        rw [if_pos (by simpa [head] using hR)]
  | psi a b c, R, hR => by
    simp only [app_psi, split]
    split
    · rfl
    · rw [split_app_low hR]

/-- **`hhi` from the shape**: the change is in the low part on both sides. -/
theorem hi_eq_of_low_change {θ P R R' : T} (hR : R = z ∨ head R < θ) (hR' : R' = z ∨ head R' < θ) :
    (split (app P R') θ).1 = (split (app P R) θ).1 := by
  rw [split_app_low hR, split_app_low hR']

/-- **`hlo` from the shape**: a nonzero low change makes a low part. -/
theorem lo_ne_of_low_change {θ P R : T} (hRz : R ≠ z) (hR : head R < θ) :
    (split (app P R) θ).2 ≠ z := by
  rw [split_app_low (Or.inr hR)]
  intro h
  exact hRz (app_eq_z h).2

end Ytosk
