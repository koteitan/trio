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

end Ytosk
