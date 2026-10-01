/-
**成分の支配つきの ≤**（落とす補題の関係）。

`DomLe μ t' t`: t' ≤ t かつ、段 u ≤ μ の t' の成分はどれも t か t の成分以下。
最後の列を落とした値 v′ と「γ_k を入れた貼り合わせの値」F′ の間でこの関係が成り立つ（実測）。
r では F′(r) = γ_{k+1} なので始点の条件（`seedOK_of_dom_gam`）になる。
-/
import Ytosk.V3Seed

namespace Ytosk

open T

/-- Domination of the components (levels `≤ μ`) together with `≤`. -/
def DomLe (μ t' t : T) : Prop :=
  t' ≤ t ∧ ∀ u, ¬ lt μ u = true → ∀ g ∈ comps u t', g ≤ t ∨ ∃ y ∈ comps u t, g ≤ y

theorem DomLe.refl (μ t : T) : DomLe μ t t :=
  ⟨le_refl t, fun _ _ g hg => Or.inr ⟨g, hg, le_refl g⟩⟩

theorem DomLe.trans {μ t1 t2 t3 : T} (h1 : DomLe μ t1 t2) (h2 : DomLe μ t2 t3) : DomLe μ t1 t3 := by
  refine ⟨le_trans h1.1 h2.1, ?_⟩
  intro u hu g hg
  rcases h1.2 u hu g hg with h | ⟨y, hy, hgy⟩
  · exact Or.inl (le_trans h h2.1)
  · rcases h2.2 u hu y hy with h | ⟨y', hy', hyy'⟩
    · exact Or.inl (le_trans hgy h)
    · exact Or.inr ⟨y', hy', le_trans hgy hyy'⟩

theorem DomLe.of_eq {μ t' t : T} (h : t' = t) : DomLe μ t' t := by rw [h]; exact DomLe.refl μ t

/-- `ψ_a` keeps the relation (same subscript). -/
theorem domle_psi {μ a y' y : T} (h : DomLe μ y' y) : DomLe μ (psi a y' z) (psi a y z) := by
  refine ⟨?_, ?_⟩
  · rcases (le_iff _ _).mp h.1 with h1 | h1
    · apply le_of_lt; rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, h1⟩
    · rw [h1]
  · intro u hu g hg
    right
    by_cases hau : lt a u = true
    · simp [comps, hau] at hg
    · have hin : ∀ w ∈ comps u y, w ∈ comps u (psi a y z) := fun w hw => mem_comps_psi_arg hau hw
      have hy : y ∈ comps u (psi a y z) := by simp [comps, hau]
      simp only [comps, hau, Bool.false_eq_true, if_false, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hg
      rcases hg with rfl | hg | hg
      · exact ⟨y, hy, h.1⟩
      · rcases h.2 u hu g hg with h' | ⟨w, hw, hgw⟩
        · exact ⟨y, hy, h'⟩
        · exact ⟨w, hin w hw, hgw⟩
      · exact ⟨g, by simp [comps, hau, hg], le_refl g⟩

/-- A prefix in front keeps the relation. -/
theorem domle_app {μ P t' t : T} (h : DomLe μ t' t) (hot : isOT (app P t) = true) :
    DomLe μ (app P t') (app P t) := by
  have htP : t ≤ app P t := by
    by_cases hP : P = z
    · subst hP; simp
    · exact le_of_lt (lt_app_right hot hP)
  refine ⟨app_le_app_left P h.1, ?_⟩
  intro u hu g hg
  rw [comps_app, List.mem_append] at hg
  rcases hg with hg | hg
  · exact Or.inr ⟨g, by rw [comps_app]; exact List.mem_append_left _ hg, le_refl g⟩
  · rcases h.2 u hu g hg with h' | ⟨w, hw, hgw⟩
    · exact Or.inl (le_trans h' htP)
    · exact Or.inr ⟨w, by rw [comps_app]; exact List.mem_append_right _ hw, hgw⟩

end Ytosk
