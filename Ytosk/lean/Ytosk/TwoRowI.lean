/-
**2 行の不変条件（保存の部品）。**

PRE をすべての枠で述べた `PreAll`: 書き換えが起きる枠（前の兄弟の状態 b ≠ 0）では、子の引数 y は b + rest（rest ≠ 0）。
経路の値が下がるだけなら PRE は保たれる（b < y′ ≤ y = b + rest ⇒ y′ = b + rest′、`pre_of_lt`）。
したがって最後の列を落としても保たれる（`preAll_take`）。
-/
import Ytosk.TwoRowFin

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **PRE at every frame.** -/
def PreAll (M : Mat) : Prop :=
  ∀ h p s y, p < M.length → par M 0 p = some h → o2r M p = psi s y z →
    lt (bst M h p) y = true → lt (psi (vr M h) z z) (psi s y z) = true →
    bst M h p ≠ z → ∃ rest, y = app (bst M h p) rest ∧ rest ≠ z

theorem PreAll.path {M : Mat} (h : PreAll M) :
    ∀ h' p s y, Anc0 M p (M.length - 1) → par M 0 p = some h' → o2r M p = psi s y z →
      lt (bst M h' p) y = true → lt (psi (vr M h') z z) (psi s y z) = true →
      bst M h' p ≠ z → ∃ rest, y = app (bst M h' p) rest ∧ rest ≠ z := by
  intro h' p s y hp hph hc h1 h2 h3
  have hpl : p < M.length := by
    have := hp.le
    rcases Nat.eq_zero_or_pos M.length with h0 | h0
    · rw [h0] at this; have := par_lt M 0 p h' hph; omega
    · omega
  exact h h' p s y hpl hph hc h1 h2 h3

/-- **A smaller argument above the state still extends the state.** -/
theorem pre_of_lt {b y y' rest : T} (hb : b < y') (hle : y' ≤ y) (hy : y = app b rest) :
    ∃ rest', y' = app b rest' ∧ rest' ≠ z := by
  subst hy
  obtain ⟨c0, rfl, hc0, _⟩ := between_app (A := b) (x := z) (y := rest) (c := y')
    (by rw [app_z_right]; exact hb) hle
  exact ⟨c0, rfl, fun h => by subst h; exact T.not_lt_z _ hc0⟩

/-- An earlier sibling of a node is not an ancestor of a later column. -/
theorem not_anc_of_earlier {M : Mat} {h c p x : Nat} (hc : par M 0 c = some h)
    (hp : par M 0 p = some h) (hcp : c < p) (hpx : p ≤ x) : ¬ Anc0 M c x := by
  intro hA
  have h1 := anc0_interval hA p hcp hpx
  obtain ⟨hhp, _, hbet⟩ := (par0_spec M).mp hp
  have hhc := par_lt M 0 c h hc
  have := hbet c hhc hcp
  omega

/-- **The state of the earlier siblings is unchanged by dropping the last column.** -/
theorem bst_take {M : Mat} {x h p : Nat} (hx : x + 1 = M.length) (hp : par M 0 p = some h)
    (hpx : p < x) : bst (M.take x) h p = bst M h p := by
  unfold bst
  have hhp := par_lt M 0 p h hp
  rw [vr_take M h (by omega), children_take]
  have hf : ((children M h).filter (fun c => decide (c < x))).filter (fun c => decide (c < p)) =
      (children M h).filter (fun c => decide (c < p)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro c _
    by_cases hc : c < p
    · simp [hc, show c < x by omega]
    · simp [hc]
  rw [hf]
  congr 2
  apply List.map_congr_left
  intro c hc
  rw [List.mem_filter] at hc
  obtain ⟨hcl, hcp⟩ := mem_children_iff.mp hc.1
  have hcp' : c < p := by simpa using hc.2
  exact o2r_take_off hx c (by omega) (not_anc_of_earlier hcp hp hcp' (by omega))

/-- **PRE at every frame survives dropping the last column.** -/
theorem preAll_take {M : Mat} (hM : 1 ≤ M.length) (hG : Good2 M)
    (hG' : Good2 (M.take (M.length - 1))) (hP : PreAll M) : PreAll (M.take (M.length - 1)) := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have hlt : (M.take (M.length - 1)).length = M.length - 1 := by rw [List.length_take]; omega
  intro h p s y hpl hph hc h1 h2 h3
  rw [hlt] at hpl
  rw [par_take M 0 p hpl] at hph
  rw [bst_take hx hph hpl] at h1 h3 ⊢
  rw [vr_take M h (by have := par_lt M 0 p h hph; omega)] at h2
  by_cases hA : Anc0 M p (M.length - 1)
  · -- on the path: the value drops with the same subscript
    have hdrop := o2r_take_anc hx hG hG' p hA hpl
    obtain ⟨w, hw⟩ := o2r_sub hG p
    obtain ⟨w', hw'⟩ := o2r_sub hG' p
    rw [hw', vr_take M p hpl] at hc
    have e := (psi.inj hc)
    obtain ⟨rfl, rfl, _⟩ := e
    rw [hw', hw, vr_take M p hpl, psi_lt_psi_z_iff] at hdrop
    have hyw : w' < w := by
      rcases hdrop with h' | ⟨_, h'⟩
      · exact absurd h' (lt_irrefl' _)
      · exact h'
    have hb : bst M h p < w' := h1
    obtain ⟨rest, hrest, _⟩ := hP h p (vr M p) w (by omega) hph hw (lt_trans hb hyw)
      (by
        have : psi (vr M h) z z < psi (vr M p) w' z := h2
        exact lt_trans this (by rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, hyw⟩)) h3
    exact pre_of_lt hb (le_of_lt hyw) hrest
  · rw [o2r_take_off hx p hpl hA] at hc
    exact hP h p s y (by omega) hph hc h1 h2 h3

end Ytosk
