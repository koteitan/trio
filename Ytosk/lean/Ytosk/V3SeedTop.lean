/-
**始点の条件を r での ◁ から出す。**

- `cof_gam`（基本列の共終性）: σ < b で σ の段 μ の成分がどれも b 未満なら、種 0 の鎖 γ_k で σ < b[γ_k] となる k がある。
  σ の成分についての帰納法と `lt_fs_psi`。
- `seedOK_of_lhd_top`: ψ_μ(σ) が標準形、σ < b、ψ_μ(σ) ◁ ψ_μ(b) なら SeedOK。
  k を「σ ≤ b[γ_k] となる最小の k」にとり、◁ を c = γ_{k+1} で使って `seedOK_of_dom_gam` に渡す。
落とした値の r での値 seed について ψ_μ(σ) ◁ ψ_μ(b) は実測で全件成立（3 行の落とす補題の一様な関係）。
-/
import Ytosk.V3Seed

namespace Ytosk

open T

section
variable {a b μ : T} (hot : isOT (psi a b z) = true) (hcb : cof b = .big μ) (hμ : ¬ lt μ a = true)
include hot hcb hμ

/-- **Cofinality of the seed-`0` chain.** -/
theorem cof_gam : ∀ n σ, size σ = n → σ < b → (∀ g ∈ comps μ σ, g < b) →
    ∃ k, σ < fs b (gamS μ b z k) := by
  have hbot : isOT b = true := isOT_arg hot
  have hmono : ∀ {j K : Nat}, j ≤ K → fs b (gamS μ b z j) ≤ fs b (gamS μ b z K) := by
    intro j K h
    rcases (le_iff _ _).mp (gamZ_le hot hcb hμ h) with h' | h'
    · exact le_of_lt (fs_mono hcb h')
    · rw [h']
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro σ hn hσ hc
    -- a common index for all components
    have hall : ∀ L : List T, (∀ g ∈ L, g ∈ comps μ σ) →
        ∃ K, ∀ g ∈ L, g < fs b (gamS μ b z K) := by
      intro L
      induction L with
      | nil => intro _; exact ⟨0, fun g hg => absurd hg (List.not_mem_nil)⟩
      | cons g L ihL =>
        intro hL
        obtain ⟨K1, hK1⟩ := ihL (fun g' hg' => hL g' (List.mem_cons_of_mem _ hg'))
        have hg := hL g List.mem_cons_self
        obtain ⟨K2, hK2⟩ := ih (size g) (hn ▸ size_comps hg) g rfl (hc g hg)
          (fun h hh => hc h (comps_trans hg h hh))
        refine ⟨max K1 K2, ?_⟩
        intro g' hg'
        rcases List.mem_cons.mp hg' with rfl | hg'
        · exact lt_of_lt_of_le hK2 (hmono (le_max_right _ _))
        · exact lt_of_lt_of_le (hK1 g' hg') (hmono (le_max_left _ _))
    obtain ⟨K, hK⟩ := hall (comps μ σ) (fun g hg => hg)
    exact ⟨K + 1, lt_fs_psi hbot hcb hσ hK⟩

/-- **The seed condition from `ψ_μ(σ) ◁ ψ_μ(b)`.** -/
theorem seedOK_of_lhd_top {σ : T} (hsot : isOT (psi μ σ z) = true) (hσb : σ < b)
    (hl : Lhd z (psi μ σ z) (psi μ b z)) : SeedOK a b μ (psi μ σ z) := by
  have hbot : isOT b = true := isOT_arg hot
  have hS0 := seedOK_z a b μ
  have hex : ∃ k, σ ≤ fs b (gamS μ b z k) := by
    obtain ⟨k, hk⟩ := cof_gam hot hcb hμ (size σ) σ rfl hσb
      (fun g hg => lt_trans (comps_lt hsot g hg) hσb)
    exact ⟨k, le_of_lt hk⟩
  classical
  let k := Nat.find hex
  have hk : σ ≤ fs b (gamS μ b z k) := Nat.find_spec hex
  have hγ : gamS μ b z k < psi μ σ z := by
    cases hkc : k with
    | zero => exact T.z_lt_psi _ _ _
    | succ j =>
      have hj : ¬ σ ≤ fs b (gamS μ b z j) := Nat.find_min hex (by omega)
      have hlt : fs b (gamS μ b z j) < σ := by
        rcases lt_trichotomy' σ (fs b (gamS μ b z j)) with h | h | h
        · exact absurd (le_of_lt h) hj
        · exact absurd (le_of_eq h) hj
        · exact h
      show psi μ (fs b (gamS μ b z j)) z < psi μ σ z
      rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, hlt⟩
  apply seedOK_of_dom_gam hot hcb hμ k hsot hγ hk
  intro u hau g hg
  have hμu : ¬ lt μ u = true := fun h => hau (show a < u from lt_of_le_of_lt (le_of_not_gt hμ) h)
  have hbin : fs b (gamS μ b z k) ∈ comps u (gamS μ b z (k + 1)) := by
    show fs b (gamS μ b z k) ∈ comps u (psi μ (fs b (gamS μ b z k)) z)
    simp [comps, hμu]
  rcases (le_iff _ _).mp hk with hlt | heq
  · have hc1 : psi μ σ z < gamS μ b z (k + 1) := by
      show psi μ σ z < psi μ (fs b (gamS μ b z k)) z
      rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, hlt⟩
    have hc2 : gamS μ b z (k + 1) ≤ psi μ b z := by
      show psi μ (fs b (gamS μ b z k)) z ≤ psi μ b z
      apply le_of_lt; rw [psi_lt_psi_z_iff]
      exact Or.inr ⟨rfl, fs_lt (gamS_valid hot hcb hμ hS0 k)⟩
    obtain ⟨y, hy, hgy⟩ := hl.2 u _ hc1 hc2 g hg
    rcases List.mem_append.mp hy with hy | hy
    · exact ⟨y, hy, hgy⟩
    · simp [Gc, comps] at hy; subst hy
      exact ⟨_, hbin, le_trans hgy (z_le _)⟩
  · refine ⟨g, ?_, le_refl g⟩
    show g ∈ comps u (psi μ (fs b (gamS μ b z k)) z)
    rw [← heq]; exact hg

end

end Ytosk
