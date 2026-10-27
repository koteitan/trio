/-
Omega preserves component domination, including the zero witness.
This pure file is below the matrix and HUAC developments.
-/
import Ytosk.FS

namespace Ytosk.OmegaComps
open T

/-- Insert a component through a visible psi node. -/
private theorem psi_mem {u v x c g : T} (hv : ¬ v < u)
    (h : g = x ∨ g ∈ comps u x ∨ g ∈ comps u v ∨ g ∈ comps u c) :
    g ∈ comps u (psi v x c) := by
  simp only [comps, List.mem_append]
  rcases h with rfl | h | h | h
  · left; rw [if_neg (show ¬ lt v u = true from hv)]; simp
  · left; rw [if_neg (show ¬ lt v u = true from hv)]; simp [h]
  · left; rw [if_neg (show ¬ lt v u = true from hv)]; simp [h]
  · right; exact h

/-- Omega changes the argument but preserves the leading index. No OT hypothesis needed. -/
theorem lev_omega_eq (X : T) : lev (omega X) = lev X := by
  unfold omega
  split
  · rename_i h
    have hh : lev X ≤ z := by
      simpa only [lev] using (lev_le_of_le (le_of_lt (show X < psi z (psi one z z) z from h)))
    exact (le_antisymm hh (z_le _)).symm
  · cases X <;> rfl

/-- Above the head index an OT term has no components. -/
theorem comps_nil_above_head {X u : T} (hX : isOT X = true) (hu : lev X < u) :
    comps u X = [] :=
  comps_eq_nil_of_lev (fun q hq => lt_of_le_of_lt
    (by
      have hh : lev (head X) = lev X := by cases X <;> rfl
      simpa only [hh] using lev_le_of_le (summands_le_head hX q hq)) hu)

/-- Omega preserves component domination; its old direct argument may grow. -/
theorem dom_comps_omega {X : T} (hX : isOT X = true) :
    ∀ u, Dom (comps u X) (comps u (omega X) ++ [z]) := by
  intro u g hg
  by_cases hE : X < E0
  · rw [omega_small hE]
    by_cases hu : u = z
    · subst u
      exact ⟨X, List.mem_append_left _ (psi_mem (T.not_lt_z _) (Or.inl rfl)),
        le_of_lt (comps_z_lt_of_lt_E0 hX hE g hg)⟩
    · have hlev : lev X = z := le_antisymm
        (by simpa only [E0, lev] using lev_le_of_le (le_of_lt hE)) (z_le _)
      have hz : z < u := by cases u with | z => exact False.elim (hu rfl) | psi => exact z_lt_psi _ _ _
      rw [comps_nil_above_head hX (by rw [hlev]; exact hz)] at hg
      simp at hg
  · cases X with
    | z => simp [comps] at hg
    | psi s b c =>
      by_cases hsu : s < u
      · rw [comps_nil_above_head hX hsu] at hg
        simp at hg
      · rw [omega_big hX hE]
        by_cases hlo : (split b (psi (succ s) z z)).2 = z
        · rw [if_pos hlo]
          have hb : (split b (psi (succ s) z z)).1 = b := by
            have h := split_app (psi (succ s) z z) b
            rw [hlo, app_z_right] at h
            exact h
          rw [hb]
          simp only [comps, if_neg (show ¬ lt s u = true from hsu), List.mem_append,
            List.mem_cons] at hg
          rcases hg with (he | hg | hg) | hg
          · subst g
            exact ⟨app b c, List.mem_append_left _ (psi_mem hsu (Or.inl rfl)), le_app_self _ _⟩
          · exact ⟨g, List.mem_append_left _ (psi_mem hsu
              (Or.inr (Or.inl (by rw [comps_app]; exact List.mem_append_left _ hg)))), le_refl _⟩
          · exact ⟨g, List.mem_append_left _ (psi_mem hsu (Or.inr (Or.inr (Or.inl hg)))), le_refl _⟩
          · exact ⟨g, List.mem_append_left _ (psi_mem hsu
              (Or.inr (Or.inl (by rw [comps_app]; exact List.mem_append_right _ hg)))), le_refl _⟩
        · rw [if_neg hlo]
          refine ⟨g, List.mem_append_left _ (psi_mem hsu (Or.inr (Or.inl ?_))), le_refl _⟩
          rw [comps_app]
          exact List.mem_append_right _ hg


end Ytosk.OmegaComps
