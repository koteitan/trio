/-
**σ = sh V V′ のもとでの成分（すべての段）（2026-10-17、t0。t2 の FDsh・t1 の QVRAsh・t0 の ClSh で共有）。**

V3Subst の `comps_sh` は段 u ≥ V（新しい段 f(u)）だけを扱う。ここでは任意の段 u′ での comps u′ (σ t) を、
元の段 u での comps u t に引き戻す。
- `comps_anti`: 段を下げると成分は増える（u ≤ u′ なら comps u′ t ⊆ comps u t）。
- `comps_sh_lev`: 段の対 (u, u′) が「u′ で見える項は u でも見える」（写される項 s > V では f(s)、写されない項 s ≤ V
  では s のまま）と u ≤ u′ を満たせば、comps u′ (σ t) の元は σ g か g（g ∈ comps u t）か、V′ のある加数の
  成分（f(s) = V′ の前置部分 + σ(s − V) の前置部分から）。
- `comps_sh_min`: 段 u := min(u′, V)（u′ ≤ V なら u′、そうでなければ V）でこの条件が立つ。
-/
import Ytosk.V3Subst

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **Lower levels have more components.** -/
theorem comps_anti {u u' : T} (h : u ≤ u') : ∀ {t g : T}, g ∈ comps u' t → g ∈ comps u t
  | z, _, hg => by simp [comps] at hg
  | psi v x c, g, hg => by
    simp only [comps, List.mem_append] at hg ⊢
    rcases hg with hg | hg
    · left
      by_cases hv : v < u'
      · rw [if_pos (show lt v u' = true from hv)] at hg; simp at hg
      · rw [if_neg (show ¬ lt v u' = true from hv)] at hg
        have hvu : ¬ v < u := fun h' => hv (lt_of_lt_of_le h' h)
        rw [if_neg (show ¬ lt v u = true from hvu)]
        simp only [List.mem_cons, List.mem_append] at hg ⊢
        rcases hg with rfl | hg | hg
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (comps_anti h hg))
        · exact Or.inr (Or.inr (comps_anti h hg))
    · exact Or.inr (comps_anti h hg)

/-- The components of a summand are components of the sum. -/
theorem comps_of_mem_summands {u : T} : ∀ {W q g : T}, q ∈ summands W → g ∈ comps u q → g ∈ comps u W
  | z, _, _, hq, _ => by simp [summands] at hq
  | psi a b c, q, g, hq, hg => by
    simp only [summands, List.mem_cons] at hq
    rcases hq with rfl | hq
    · simp only [comps, List.mem_append] at hg ⊢
      rcases hg with hg | hg
      · exact Or.inl hg
      · simp [comps] at hg
    · simp only [comps, List.mem_append]
      exact Or.inr (comps_of_mem_summands hq hg)

/-- A component of a sum is a component of one of its summands. -/
theorem comps_to_summand {u : T} : ∀ {W g : T}, g ∈ comps u W → ∃ q ∈ summands W, g ∈ comps u q
  | z, _, hg => by simp [comps] at hg
  | psi a b c, g, hg => by
    simp only [comps, List.mem_append] at hg
    rcases hg with hg | hg
    · exact ⟨psi a b z, by simp [summands], by simp only [comps, List.mem_append]; exact Or.inl hg⟩
    · obtain ⟨q, hq, hgq⟩ := comps_to_summand hg
      exact ⟨q, by simp [summands, hq], hgq⟩

/-- The parts of `comps u (ψ_v(x) + c)` when `ψ_v(x)` is seen at `u`. -/
theorem mem_comps_psi_of {u v x c g : T} (hv : ¬ v < u)
    (h : g = x ∨ g ∈ comps u x ∨ g ∈ comps u v ∨ g ∈ comps u c) : g ∈ comps u (psi v x c) := by
  simp only [comps, List.mem_append]
  rcases h with rfl | h | h | h
  · left; rw [if_neg (show ¬ lt v u = true from hv)]; simp
  · left; rw [if_neg (show ¬ lt v u = true from hv)]; simp [h]
  · left; rw [if_neg (show ¬ lt v u = true from hv)]; simp [h]
  · right; exact h

theorem mem_comps_tail {u v x c g : T} (h : g ∈ comps u c) : g ∈ comps u (psi v x c) := by
  simp only [comps, List.mem_append]; exact Or.inr h

/-- **The components of `σ t` at any level**, pulled back to a level `u` of `t`. -/
theorem comps_sh_lev (V V' : T) {u u' : T}
    (hC1 : ∀ s, V < s → ¬ shf V V' s < u' → ¬ s < u)
    (hC2 : ∀ s, ¬ V < s → ¬ s < u' → ¬ s < u)
    (hC3 : u ≤ u') :
    ∀ (n : Nat) (t g' : T), size t ≤ n → g' ∈ comps u' (sh V V' t) →
      (∃ g ∈ comps u t, g' = sh V V' g) ∨ (∃ g ∈ comps u t, g' = g) ∨
        (∃ q ∈ summands V', g' ∈ comps u' q)
  | 0, t, g', hn, hg => by
    cases t with
    | z => simp [comps] at hg
    | psi => simp [size] at hn
  | n + 1, t, g', hn, hg => by
    cases t with
    | z => simp [comps] at hg
    | psi s y c =>
      have hny : size y ≤ n := by simp [size] at hn; omega
      have hnc : size c ≤ n := by simp [size] at hn; omega
      have hns : size (sub s V) ≤ n := by have := size_sub_le s V; simp [size] at hn; omega
      -- the tail
      have htail : g' ∈ comps u' (sh V V' c) →
          (∃ g ∈ comps u (psi s y c), g' = sh V V' g) ∨ (∃ g ∈ comps u (psi s y c), g' = g) ∨
            (∃ q ∈ summands V', g' ∈ comps u' q) := by
        intro h
        rcases comps_sh_lev V V' hC1 hC2 hC3 n c g' hnc h with ⟨g, hg, e⟩ | ⟨g, hg, e⟩ | h
        · exact Or.inl ⟨g, mem_comps_tail hg, e⟩
        · exact Or.inr (Or.inl ⟨g, mem_comps_tail hg, e⟩)
        · exact Or.inr (Or.inr h)
      by_cases hVs : V < s
      · rw [sh_psi_gt hVs] at hg
        simp only [comps, List.mem_append] at hg
        rcases hg with hg | hg
        · by_cases hf : shf V V' s < u'
          · rw [if_pos (show lt (shf V V' s) u' = true from hf)] at hg; simp at hg
          · rw [if_neg (show ¬ lt (shf V V' s) u' = true from hf)] at hg
            have hsu := hC1 s hVs hf
            simp only [List.mem_cons, List.mem_append] at hg
            rcases hg with rfl | hg | hg
            · exact Or.inl ⟨y, mem_comps_psi_of hsu (Or.inl rfl), rfl⟩
            · rcases comps_sh_lev V V' hC1 hC2 hC3 n y g' hny hg with ⟨g, hg, e⟩ | ⟨g, hg, e⟩ | h
              · exact Or.inl ⟨g, mem_comps_psi_of hsu (Or.inr (Or.inl hg)), e⟩
              · exact Or.inr (Or.inl ⟨g, mem_comps_psi_of hsu (Or.inr (Or.inl hg)), e⟩)
              · exact Or.inr (Or.inr h)
            · -- the components of `f(s) = V′ + σ(s − V)`
              unfold shf at hg
              obtain ⟨P, hP, hPs⟩ := add_eq_app_prefix V' (sh V V' (sub s V))
              rw [hP, comps_app] at hg
              rcases List.mem_append.mp hg with hg | hg
              · obtain ⟨q, hq, hgq⟩ := comps_to_summand hg
                exact Or.inr (Or.inr ⟨q, hPs q hq, hgq⟩)
              · rcases comps_sh_lev V V' hC1 hC2 hC3 n (sub s V) g' hns hg with ⟨g, hg, e⟩ | ⟨g, hg, e⟩ | h
                · exact Or.inl ⟨g, mem_comps_psi_of hsu (Or.inr (Or.inr (Or.inl (comps_sub_sub u s V hg)))), e⟩
                · exact Or.inr (Or.inl ⟨g, mem_comps_psi_of hsu
                    (Or.inr (Or.inr (Or.inl (comps_sub_sub u s V hg)))), e⟩)
                · exact Or.inr (Or.inr h)
        · exact htail hg
      · rw [sh_psi_le hVs] at hg
        simp only [comps, List.mem_append] at hg
        rcases hg with hg | hg
        · by_cases hf : s < u'
          · rw [if_pos (show lt s u' = true from hf)] at hg; simp at hg
          · rw [if_neg (show ¬ lt s u' = true from hf)] at hg
            have hsu := hC2 s hVs hf
            simp only [List.mem_cons, List.mem_append] at hg
            rcases hg with e | hg | hg
            · exact Or.inr (Or.inl ⟨y, mem_comps_psi_of hsu (Or.inl rfl), e⟩)
            · exact Or.inr (Or.inl ⟨g', mem_comps_psi_of hsu (Or.inr (Or.inl (comps_anti hC3 hg))), rfl⟩)
            · exact Or.inr (Or.inl ⟨g', mem_comps_psi_of hsu (Or.inr (Or.inr (Or.inl (comps_anti hC3 hg)))), rfl⟩)
        · exact htail hg

/-- **The pull-back level `min(u′, V)`** satisfies the conditions of `comps_sh_lev`. -/
theorem comps_sh_min (V V' : T) (u' : T) {t g' : T} (hg : g' ∈ comps u' (sh V V' t)) :
    let u := if u' ≤ V then u' else V
    (∃ g ∈ comps u t, g' = sh V V' g) ∨ (∃ g ∈ comps u t, g' = g) ∨ (∃ q ∈ summands V', g' ∈ comps u' q) := by
  intro u
  apply comps_sh_lev V V' (u := u) (u' := u') _ _ _ (size t) t g' (Nat.le_refl _) hg
  · intro s hVs _
    by_cases h : u' ≤ V
    · show ¬ s < (if u' ≤ V then u' else V)
      rw [if_pos h]; exact fun h' => absurd (lt_of_lt_of_le h' h) (not_lt.mpr (le_of_lt hVs))
    · show ¬ s < (if u' ≤ V then u' else V)
      rw [if_neg h]; exact fun h' => absurd h' (not_lt.mpr (le_of_lt hVs))
  · intro s hVs hsu
    by_cases h : u' ≤ V
    · show ¬ s < (if u' ≤ V then u' else V)
      rw [if_pos h]; exact hsu
    · exfalso
      exact h (le_trans (not_lt.mp hsu) (not_lt.mp hVs))
  · show (if u' ≤ V then u' else V) ≤ u'
    by_cases h : u' ≤ V
    · rw [if_pos h]
    · rw [if_neg h]; exact le_of_lt (lt_of_not_ge h)

end Ytosk
