/-
**3 行・t = 1・q = r: 添字が μ より小さい始点の SeedOK を ◁ から出す。**

A = ψ_μ(B)、B = b + Ω_{μ+1}、seed = ψ_s(σ)（s < μ）で seed ◁ A とする。
- dom: c0 ∈ (b + seed, B] は c0 = b + e（seed < e ≤ Ω_{μ+1}）。e ≤ A なら ◁ を c = e に当てる。e > A なら e の添字は
  μ か μ + 1 なので e の成分は μ の成分を含み、◁ を c = Ω_μ に当てる（`seedOK_of_lhd_below`）。
- comps_a（段 a の成分が b + seed より小さい）は仮定として受ける。
-/
import Ytosk.V3QRSeed
import Ytosk.V3SeedTop

namespace Ytosk

open T

/-- The components of `μ` are components of a `ψ` with subscript `μ` or `μ + 1`. -/
theorem comps_sub_of_psi {μ w f h u : T} (hw : w = μ ∨ w = succ μ) (hu : ¬ lt μ u = true) :
    ∀ y ∈ comps u μ, y ∈ comps u (psi w f h) := by
  intro y hy
  have hwu : ¬ lt w u = true := by
    rcases hw with rfl | rfl
    · exact hu
    · intro h
      exact hu (show μ < u from lt_trans (lt_succ_self μ) (show succ μ < u from h))
  simp only [comps, List.mem_append]
  left
  rw [if_neg hwu]
  rcases hw with rfl | rfl
  · simp [hy]
  · simp [succ, comps_app, hy]

/-- **SeedOK below the top subscript from `◁`** (the components at the level `a` are given). -/
theorem seedOK_of_lhd_below {a b μ s σ : T} (ha : ¬ lt μ a = true)
    (hsot : isOT (psi s σ z) = true) (hsμ : s < μ)
    (hl : Lhd z (psi s σ z) (psi μ (app b (psi (succ μ) z z)) z))
    (hca : ∀ g ∈ comps a (psi s σ z), g < app b (psi s σ z)) :
    SeedOK a (app b (psi (succ μ) z z)) μ (psi s σ z) := by
  refine ⟨hsot, ?_, ?_, ?_, ?_⟩
  · rw [psi_lt_psi_z_iff]; exact Or.inl (lt_trans hsμ (lt_succ_self μ))
  · rw [fs_br, psi_lt_psi_z_iff]; exact Or.inl hsμ
  · rw [fs_br]; exact hca
  · intro u c0 c1 h1 h2 hu g hg
    rw [fs_br] at h1
    have hμu : ¬ lt μ u = true := fun h =>
      hu (show a < u from lt_of_le_of_lt (le_of_not_gt (show ¬ μ < a from ha)) (show μ < u from h))
    obtain ⟨e, rfl, he1, he2⟩ := between_app h1 h2
    -- the components of `e` are components of `ψ_a(b + e) + c1`
    have hsub : ∀ y ∈ comps u e, y ∈ comps u (psi a (app b e) c1) := by
      intro y hy
      simp only [comps, List.mem_append]
      left
      rw [if_neg hu]
      simp [comps_app, hy]
    have hlift : ∀ c, psi s σ z < c → c ≤ psi μ (app b (psi (succ μ) z z)) z →
        (∀ y ∈ comps u c, y = z ∨ y ∈ comps u e) →
        ∃ y ∈ comps u (psi a (app b e) c1) ++ Gc u z, g ≤ y := by
      intro c hc1 hc2 hce
      obtain ⟨y, hy, hgy⟩ := hl.2 u c hc1 hc2 g hg
      rcases List.mem_append.mp hy with hy | hy
      · rcases hce y hy with rfl | hy'
        · exact ⟨z, List.mem_append_right _ (by simp [Gc]), hgy⟩
        · exact ⟨y, List.mem_append_left _ (hsub y hy'), hgy⟩
      · exact ⟨y, List.mem_append_right _ hy, hgy⟩
    by_cases heA : e ≤ psi μ (app b (psi (succ μ) z z)) z
    · exact hlift e he1 heA (fun y hy => Or.inr hy)
    · -- `e` has subscript `μ` or `μ + 1`
      have hAe : psi μ (app b (psi (succ μ) z z)) z < e := lt_of_not_ge heA
      cases e with
      | z => exact absurd hAe (T.not_lt_z _)
      | psi w f h =>
        have hw : w = μ ∨ w = succ μ := by
          have h1' := hAe
          rw [T.psi_lt_psi] at h1'
          have hμw : μ ≤ w := by
            rcases h1' with h' | ⟨h', _⟩ | ⟨h', _, _⟩
            · exact le_of_lt h'
            · rw [h']
            · rw [h']
          rcases (le_iff _ _).mp he2 with h' | h'
          · rw [T.psi_lt_psi] at h'
            rcases h' with h' | ⟨h', h''⟩ | ⟨_, _, h''⟩
            · left
              have := lt_succ_iff.mp h'
              exact le_antisymm this hμw
            · right; exact h'
            · exact absurd h'' (T.not_lt_z _)
          · simp only [psi.injEq] at h'; right; exact h'.1
        have hB0 : z < app b (psi (succ μ) z z) := by
          cases b with
          | z => exact T.z_lt_psi _ _ _
          | psi => exact T.z_lt_psi _ _ _
        refine hlift (psi μ z z) (by rw [psi_lt_psi_z_iff]; exact Or.inl hsμ)
          (le_of_lt (by rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, hB0⟩)) ?_
        intro y hy
        simp only [comps, List.mem_append, List.not_mem_nil, or_false] at hy
        rw [if_neg hμu] at hy
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, false_or] at hy
        rcases hy with rfl | hy
        · exact Or.inl rfl
        · exact Or.inr (comps_sub_of_psi hw hμu y hy)

end Ytosk
