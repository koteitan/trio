/-
**落とす補題: v が変わる枠。**

`lhd_psi_sub`: 引数 0 の o（v だけ変わる o の枠、実測で引数はいつも 0）は、添字の ◁ から ψ の値の ◁。
-/
import Ytosk.V3DropNode

namespace Ytosk

open T

/-- **The subscript route**: `v′ ◁ v` gives `ψ_{v′}(0) ◁ ψ_v(0)`. -/
theorem lhd_psi_sub {η v' v : T} (h : Lhd η v' v) : Lhd η (psi v' z z) (psi v z z) := by
  refine ⟨by rw [psi_lt_psi_z_iff]; exact Or.inl h.1, fun u c h1 h2 => ?_⟩
  cases c with
  | z => exact absurd h1 (T.not_lt_z _)
  | psi w Y R =>
    -- the subscript `w` of `c` lies in `[v', v]`
    have hw1 : v' ≤ w := by
      rw [T.psi_lt_psi] at h1
      rcases h1 with h1 | ⟨rfl, _⟩ | ⟨rfl, _, _⟩
      · exact le_of_lt h1
      · exact le_refl _
      · exact le_refl _
    have hw2 : w ≤ v := by
      rcases (le_iff _ _).mp h2 with h3 | h3
      · rw [T.psi_lt_psi] at h3
        rcases h3 with h4 | ⟨_, h4⟩ | ⟨h4, _, _⟩
        · exact le_of_lt h4
        · exact absurd h4 (T.not_lt_z _)
        · rw [h4]
      · simp only [psi.injEq] at h3
        rw [h3.1]
    intro g hg
    simp only [comps, List.mem_append, List.not_mem_nil, or_false] at hg
    split at hg
    · simp at hg
    · rename_i hv'u
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, false_or] at hg
      rcases hg with rfl | hg
      · exact ⟨z, List.mem_append_right _ (by simp [Gc]), le_refl _⟩
      · have hwu : ¬ lt w u = true := by
          intro hw
          apply hv'u
          rcases (le_iff _ _).mp hw1 with hw1 | rfl
          · exact lt_trans hw1 hw
          · exact hw
        have hsub : ∀ t ∈ comps u w, t ∈ comps u (psi w Y R) := by
          intro t ht
          simp only [comps, List.mem_append]
          left
          rw [if_neg hwu]
          simp [ht]
        rcases (le_iff _ _).mp hw1 with hw1 | rfl
        · obtain ⟨y, hy, hgy⟩ := h.2 u w hw1 hw2 g hg
          rcases List.mem_append.mp hy with hy | hy
          · exact ⟨y, List.mem_append_left _ (hsub y hy), hgy⟩
          · exact ⟨y, List.mem_append_right _ hy, hgy⟩
        · exact ⟨g, List.mem_append_left _ (hsub g hg), le_refl _⟩

theorem lhdE_psi_sub {v' v : T} (h : LhdE v' v) : LhdE (psi v' z z) (psi v z z) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (lhd_psi_sub h)

/-- `1 ◁ l` for every `l > 1`. -/
theorem lhd_one {η l : T} (hl : one < l) : Lhd η one l := by
  refine ⟨hl, fun u c _ _ g hg => ?_⟩
  simp only [one, comps, List.append_nil] at hg
  split at hg
  · simp at hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rw [hg]
    exact ⟨z, List.mem_append_right _ (by simp [Gc]), le_refl _⟩

theorem lhdE_one {l : T} (hl : one ≤ l) : LhdE one l := by
  rcases (le_iff _ _).mp hl with h | h
  · exact Or.inr (lhd_one h)
  · exact Or.inl h

/-- **The `q` frame**: dropping the leaf `x` (`o(x) = ψ_s(0)`, no rewrite) after a `◁` of the earlier part. -/
theorem lhdE_oq {v X' B s : T} (hX : LhdE X' B) :
    LhdE (psi v X' z) (psi v (app B (psi s z z)) z) :=
  LhdE.trans (lhdE_psi v hX) (lhdE_psi v (lhdE_prefix B _))

/-- The step of a leaf child never rewrites. -/
theorem step_leaf (a B s : T) : step a B s z z = add B (psi s z z) := by
  unfold step
  rw [if_neg (by simp [lt])]

/-- **The `q` frame, with `v` changing too**: `ψ_{v′}(0) ◁ ψ_v(X)` from `v′ ◁ v`. -/
theorem lhdE_oq_v {v' v X : T} (hv : LhdE v' v) : LhdE (psi v' z z) (psi v X z) := by
  apply LhdE.trans (lhdE_psi_sub hv)
  by_cases hX : X = z
  · subst hX; exact Or.inl rfl
  · exact Or.inr (lhd_psi v (lhd_zero hX))

/-- **The upgrade frame**: `V + l′ ◁ V + l` from `l′ ◁ l`, without absorption. -/
theorem lhdE_vupg {V l' l : T} (hl : LhdE l' l) : LhdE (app V l') (app V l) := lhdE_app V hl

end Ytosk
