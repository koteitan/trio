/-
**始点の条件の一般化**: σ ≤ b[0] の代わりに、種 0 の鎖 γ_k = gamS μ b 0 k で σ ≤ b[γ_k] かつ γ_k < ψ_μ(σ)
（3 行では Ω_{Ω_1}[0] = 1 のように添字がつぶれて σ ≤ b[0] が崩れる。実測で k ≤ 2）。
-/
import Ytosk.V3MainT1

namespace Ytosk

open T

theorem seedOK_of_lhd_gam {a b μ σ : T} (hot : isOT (psi a b z) = true) (hcb : cof b = .big μ)
    (hμ : ¬ lt μ a = true) (hsot : isOT (psi μ σ z) = true) (k : Nat) (hσ : σ ≤ fs b (gamS μ b z k)) (hγ : gamS μ b z k < psi μ σ z)
    (hl : Lhd z σ b) :
    SeedOK a b μ (psi μ σ z) := by
  have hbot : isOT b = true := isOT_arg hot
  have hcomp := comps_lt hot
  have hS0 := seedOK_z a b μ
  have hmono : fs b (gamS μ b z k) < fs b (psi μ σ z) := fs_mono hcb hγ
  have hσlt : σ < fs b (psi μ σ z) := lt_of_le_of_lt hσ hmono
  have hslt : psi μ σ z < psi (succ μ) z z := by
    rw [psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self μ)
  have hval : ValidLt b (psi μ σ z) := by unfold ValidLt; rw [hcb]; exact hslt
  have hfsle : fs b (psi μ σ z) ≤ b := le_of_lt (fs_lt hval)
  have hge : psi μ z z ≤ psi μ σ z := by
    rw [le_iff]
    rcases (le_iff _ _).mp (z_le σ) with h4 | h4
    · left; rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, h4⟩
    · right; rw [← h4]
  -- the Denis node `ψ_a(b[0])` is standard
  have hd0 : isOT (psi a (fs b (gamS μ b z k)) z) = true := isOT_diag_seed hot hcb hμ hS0 k
  have hcd0 := comps_lt hd0
  refine ⟨hsot, hslt, ?_, ?_, ?_⟩
  · rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, hσlt⟩
  · intro g hg
    simp only [comps, hμ, Bool.false_eq_true, if_false, List.mem_append, List.mem_cons] at hg
    rcases hg with (rfl | hg | hg) | hg
    · exact hσlt
    · -- a component of `σ`: dominated by components of `b[0]`
      rcases (le_iff _ _).mp hσ with hlt | heq
      · obtain ⟨y, hy, hgy⟩ := hl.2 a (fs b (gamS μ b z k)) hlt (le_of_lt (fs_lt (by
          unfold ValidLt; rw [hcb]; exact gamS_lt_om hot hcb hμ hS0 k))) g hg
        rcases List.mem_append.mp hy with hy | hy
        · exact lt_of_le_of_lt hgy (lt_trans (hcd0 y hy) hmono)
        · simp [Gc, comps] at hy; subst hy
          exact lt_of_le_of_lt hgy (lt_of_le_of_lt (z_le _) hmono)
      · rw [heq] at hg; exact lt_trans (hcd0 g hg) hmono
    · have hgb : g ∈ comps a b := comps_mu hbot hcb hge hslt hfsle (le_refl b) hμ g hg
      have hgb' := hcomp g hgb
      by_contra hcon
      have hgy : g ∈ comps a g := comps_mu hbot hcb hge hslt (le_of_not_gt hcon) (le_of_lt hgb') hμ g hg
      exact Nat.lt_irrefl _ (size_comps hgy)
    · simp at hg
  · intro u c0 c1 h1 h2 hau g hg
    have hμu : ¬ lt μ u = true := fun h => hau (show a < u from lt_of_le_of_lt (le_of_not_gt hμ) h)
    have hin : ∀ w ∈ comps u c0, w ∈ comps u (psi a c0 c1) := fun w hw => mem_comps_psi_arg hau hw
    have hc0in : c0 ∈ comps u (psi a c0 c1) := by simp [comps, hau]
    simp only [comps, hμu, Bool.false_eq_true, if_false, List.mem_append, List.mem_cons] at hg
    rcases hg with (rfl | hg | hg) | hg
    · exact ⟨c0, List.mem_append_left _ hc0in, le_of_lt (lt_trans hσlt h1)⟩
    · obtain ⟨y, hy, hgy⟩ := hl.2 u c0 (lt_trans hσlt h1) h2 g hg
      rcases List.mem_append.mp hy with hy | hy
      · exact ⟨y, List.mem_append_left _ (hin y hy), hgy⟩
      · exact ⟨y, List.mem_append_right _ (by simpa [Gc, comps] using hy), hgy⟩
    · have := comps_mu hbot hcb hge hslt (le_of_lt h1) h2 hμu g hg
      exact ⟨g, List.mem_append_left _ (hin g this), le_refl _⟩
    · simp at hg


end Ytosk
