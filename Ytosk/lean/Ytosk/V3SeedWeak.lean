/-
**t = 1・q = r: 弱く下がった始点の SeedOK（2026-10-17、t1）。**

drop の報告（t2ext の標準形 1 件）: q = r で r が M では祖先へ上げられ、M.take x では上げを失うと、
始点 seed = o′(r) = Ω_{w′}（w′ = v′(r) < μ = v(r)）は o(r) に ◁ で下がらない（V3QRFinal3 の hlhd が偽）。
落とす補題はこの r で PO の弱い枝（seed = ψ_{w′}(0)）と PV の弱い枝（WCSP: w′ の成分は可算など）を与える。
w′ の成分がどれも Ω_{w′} 未満（`SmallSelf`、可算 CS はその特別な場合）なら、◁ を使わずに SeedOK を出す（`seedOK_of_small_below`）。
dom: 段 u の seed の成分は 0 か w′ の成分（< Ω_1 ≤ seed ≤ b + seed < c0）で、c0 は ψ_a(c0) + c1 の成分。
-/
import Ytosk.V3SeedLhd

namespace Ytosk

open T

/-- A term below every summand of `b` is at most `b + t`. -/
theorem le_app_of_allGe {θ t : T} (ht : t < θ) : ∀ {b : T}, AllGeT θ b → t ≤ app b t
  | z, _ => le_refl _
  | psi a1 b1 c1, hb => by
    have hθ : ¬ psi a1 b1 z < θ := hb _ (by simp [summands])
    have hlt : t < psi a1 b1 z := lt_of_lt_of_le ht (le_of_not_gt hθ)
    apply le_of_lt
    show t < psi a1 b1 (app c1 t)
    cases t with
    | z => exact z_lt_psi _ _ _
    | psi s σ τ =>
      rw [psi_lt_psi] at hlt ⊢
      rcases hlt with h | ⟨h1, h2⟩ | ⟨_, _, h3⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · exact absurd h3 (T.not_lt_z _)

/-- The components of `w` are below `Ω_w`. -/
def SmallSelf (w : T) : Prop := ∀ g ∈ comps z w, g < psi w z z

theorem SmallSelf.of_cs {w : T} (h1w : one ≤ w) (hcs : CS w) : SmallSelf w := by
  intro g hg
  have hg1 : g < psi one z z := hcs g hg
  have hΩ : psi one z z ≤ psi w z z := by
    rcases (le_iff _ _).mp h1w with h | rfl
    · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h))
    · exact le_refl _
  exact lt_of_lt_of_le hg1 hΩ

/-- **SeedOK for a weakly dropped seed `Ω_{w′}`** (`w′ < μ`, the components of `w′` below `Ω_{w′}`). -/
theorem seedOK_of_small_below {a b μ w : T} (hb : AllGeT (psi (succ μ) z z) b)
    (hsot : isOT (psi w z z) = true) (hwμ : w < μ) (hsm : SmallSelf w)
    (hca : ∀ g ∈ comps a (psi w z z), g < app b (psi w z z)) :
    SeedOK a (app b (psi (succ μ) z z)) μ (psi w z z) := by
  refine ⟨hsot, ?_, ?_, ?_, ?_⟩
  · rw [psi_lt_psi_z_iff]; exact Or.inl (lt_trans hwμ (lt_succ_self μ))
  · rw [fs_br, psi_lt_psi_z_iff]; exact Or.inl hwμ
  · rw [fs_br]; exact hca
  · intro u c0 c1 h1 _ hu g hg
    rw [fs_br] at h1
    have hseedθ : psi w z z < psi (succ μ) z z := by
      rw [psi_lt_psi_z_iff]; exact Or.inl (lt_trans hwμ (lt_succ_self μ))
    have hle := le_app_of_allGe hseedθ hb
    have hmem : c0 ∈ comps u (psi a c0 c1) ++ Gc u z := by
      apply List.mem_append_left
      simp only [comps, List.mem_append]
      left; rw [if_neg hu]; simp
    have hg0 := comps_sub_z u _ g hg
    simp only [comps, List.mem_append] at hg0
    have hgw : g = z ∨ g ∈ comps z w := by
      rcases hg0 with h | h
      · split at h
        · simp at h
        · simp only [List.mem_cons, List.mem_append] at h
          rcases h with h | h | h
          · exact Or.inl h
          · simp at h
          · exact Or.inr h
      · simp at h
    rcases hgw with rfl | hgw
    · exact ⟨z, List.mem_append_right _ (by simp [Gc]), le_refl _⟩
    · exact ⟨c0, hmem, le_of_lt (lt_of_lt_of_le (hsm g hgw) (le_trans hle (le_of_lt h1)))⟩

/-- **SeedOK for a weakly dropped seed `Ω_{w′}`** (`w′ < μ`, countable components of `w′`). -/
theorem seedOK_of_cs_below {a b μ w : T} (_ha : ¬ lt μ a = true) (hb : AllGeT (psi (succ μ) z z) b)
    (hsot : isOT (psi w z z) = true) (hwμ : w < μ) (h1w : one ≤ w) (hcs : CS w)
    (hca : ∀ g ∈ comps a (psi w z z), g < app b (psi w z z)) :
    SeedOK a (app b (psi (succ μ) z z)) μ (psi w z z) :=
  seedOK_of_small_below hb hsot hwμ (SmallSelf.of_cs h1w hcs) hca

end Ytosk
