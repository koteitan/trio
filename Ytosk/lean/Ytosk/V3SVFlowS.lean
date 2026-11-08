/-
**t = 2, sv: the tree facts for the flow of `T2SVStrict` (2026-11-08).**

`EndAt M w e`: `e` is the last column of the subtree of `w` (subtrees are intervals, `anc_between`).
The first child of `w` is `w + 1`; between two adjacent children `s < j` of `w` the subtree of `s` is `[s, j − 1]`;
the last child of `w` ends where `w` ends.
-/
import Ytosk.V3SVFlow

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- `e` is the last column of the subtree of `w`. -/
def EndAt (M : Mat) (w e : Nat) : Prop :=
  w ≤ e ∧ (∀ t, w ≤ t → t ≤ e → Anc0 M w t) ∧ ¬ Anc0 M w (e + 1)

/-- Two different children of one column are not ancestors of each other. -/
theorem not_anc_sib {M : Mat} {w c j : Nat} (hc : c ∈ children M w) (hj : j ∈ children M w) (hne : c ≠ j) :
    ¬ Anc0 M c j := by
  intro hA
  have hpj : par M 0 j = some w := (mem_children_iff.mp hj).2
  have h1 := (anc0_of_par_ne hA hne hpj).le
  have h2 := (mem_children hc).1
  omega

/-- The child of `w` on the way to a proper descendant. -/
theorem child_toward {M : Mat} {w t : Nat} (hA : Anc0 M w t) (hne : w ≠ t) (ht : t < M.length) :
    ∃ c ∈ children M w, Anc0 M c t := by
  obtain ⟨c, hpc, hct⟩ := anc0_child hA hne
  exact ⟨c, mem_children_iff.mpr ⟨by have := hct.le; omega, hpc⟩, hct⟩

/-- **The first child is the next column.** -/
theorem first_child {M : Mat} {w j : Nat} (hj : j ∈ children M w) : w + 1 ∈ children M w := by
  have hA := anc0_of_child hj
  have hwj := (mem_children hj).1
  have hjM := (mem_children hj).2
  have hA1 : Anc0 M w (w + 1) := anc_between hA (w + 1) (by omega) (by omega)
  obtain ⟨c, hc, hcA⟩ := child_toward hA1 (by omega) (by omega)
  have h1 := hcA.le
  have h2 := (mem_children hc).1
  have : c = w + 1 := by omega
  rw [← this]; exact hc

/-- **Adjacent children**: the subtree of `s` is `[s, j − 1]`. -/
theorem endAt_sib {M : Mat} {w s j : Nat} (hs : s ∈ children M w) (hj : j ∈ children M w) (hsj : s < j)
    (hnb : ∀ c ∈ children M w, ¬ (s < c ∧ c < j)) : EndAt M s (j - 1) := by
  have hjM := (mem_children hj).2
  have hwA := anc0_of_child hj
  refine ⟨by omega, fun t hst htj => ?_, ?_⟩
  · by_cases hts : t = s
    · rw [hts]; exact Anc0.refl s
    have hws := (mem_children hs).1
    have hwt : Anc0 M w t := anc_between hwA t (by omega) (by omega)
    obtain ⟨c, hc, hct⟩ := child_toward hwt (by omega) (by omega)
    have hcs : c = s := by
      have hct' := hct.le
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact not_anc_sib hc hs (by omega) (anc_between hct s (by omega) (by omega))
      · exact hnb c hc ⟨hgt, by omega⟩
    rw [← hcs]; exact hct
  · rw [show j - 1 + 1 = j by omega]
    exact not_anc_sib hs hj (by omega)

/-- **The last child ends where its parent ends.** -/
theorem endAt_last {M : Mat} {w l e : Nat} (hl : l ∈ children M w) (hmax : ∀ c ∈ children M w, c ≤ l)
    (he : EndAt M w e) (heM : e < M.length) : EndAt M l e := by
  obtain ⟨hwe, hall, hnot⟩ := he
  have hlA := anc0_of_child hl
  have hle : l ≤ e := by
    by_contra h
    exact hnot (anc_between hlA (e + 1) (by omega) (by omega))
  refine ⟨hle, fun t hlt hte => ?_, fun hA => hnot (Anc0.trans hlA hA)⟩
  have hwt := hall t (by have := (mem_children hl).1; omega) hte
  have hne : w ≠ t := by have := (mem_children hl).1; omega
  obtain ⟨c, hc, hct⟩ := child_toward hwt hne (by omega)
  have hcl := hmax c hc
  rcases Nat.eq_or_lt_of_le hcl with rfl | hlt'
  · exact hct
  · exact absurd (anc_between hct l (by omega) (by omega)) (not_anc_sib hc hl (by omega))

/-- **A leaf ends at itself.** -/
theorem endAt_leaf {M : Mat} {w e : Nat} (he : EndAt M w e) (heM : e < M.length)
    (hnil : ∀ c, c ∈ children M w → False) : w = e := by
  obtain ⟨hwe, hall, _⟩ := he
  by_contra hne
  have hA1 := hall (w + 1) (by omega) (by omega)
  obtain ⟨c, hc, hcA⟩ := child_toward hA1 (by omega) (by omega)
  exact hnil c hc

/-- **The end of a subtree that is followed by a sibling has no children.** -/
theorem end_no_child {M : Mat} {s j : Nat} (he : EndAt M s (j - 1)) (hsj : s < j) (hjM : j < M.length) :
    ∀ c, c ∈ children M (j - 1) → False := by
  intro c hc
  obtain ⟨_, hall, hnot⟩ := he
  have hjc := (mem_children hc).1
  have hA : Anc0 M (j - 1) c := anc0_of_child hc
  have hAj : Anc0 M (j - 1) j := anc_between hA j (by omega) (by omega)
  rw [show j - 1 + 1 = j by omega] at hnot
  exact hnot (Anc0.trans (hall (j - 1) (by omega) le_rfl) hAj)

end Ytosk.V3Main.SeedPF
