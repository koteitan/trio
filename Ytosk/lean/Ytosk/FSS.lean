/-
**始点つきの対角化（補題 3.3 の一般化）。**

対角化の点 ψ_a(b)（cof b = Ω_{μ+1}、μ ≥ a）で、Denis 氏の列 γ_0 = 0 の代わりに始点 γ′_0 = 始点から
γ′_{k+1} = ψ_μ(b[γ′_k]) とする。展開 M[n] では始点は M[1] での r の値（最後のコピーには上げ役がないので 0 にならない）。
始点の条件（`SeedOK`）のもとで、列の各項 ψ_a(b[γ′_m]) は標準形で、◁ 関係を `Gc` が自明な形で満たす
（したがって上の ω の段の標準形も添字の成分の条件なしで出る）。
-/
import Ytosk.FSD

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- The seeded diagonal chain at `μ`: `γ′_0 = seed`, `γ′_{k+1} = ψ_μ(b[γ′_k])`. -/
def gamS (μ b seed : T) : Nat → T
  | 0 => seed
  | k + 1 => psi μ (fs b (gamS μ b seed k)) z

/-- The conditions on the seed at the diagonal node `ψ_a(b)`. -/
structure SeedOK (a b μ seed : T) : Prop where
  ot : isOT seed = true
  lt_om : seed < psi (succ μ) z z
  lt_next : seed < psi μ (fs b seed) z
  comps_a : ∀ g ∈ comps a seed, g < fs b seed
  dom : ∀ u c0 c1, fs b seed < c0 → c0 ≤ b → ¬ lt a u = true →
    ∀ g ∈ comps u seed, ∃ y ∈ comps u (psi a c0 c1) ++ Gc u z, g ≤ y

section chain
variable {a b μ seed : T} (hot : isOT (psi a b z) = true) (hcb : cof b = .big μ)
  (hμ : ¬ lt μ a = true) (hS : SeedOK a b μ seed)
include hot hcb hμ hS

theorem gamS_lt_om : ∀ k, gamS μ b seed k < psi (succ μ) z z
  | 0 => hS.lt_om
  | k + 1 => by
    show psi μ _ z < _
    rw [psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self μ)

theorem gamS_valid : ∀ k, ValidLt b (gamS μ b seed k) := fun k => by
  unfold ValidLt; rw [hcb]; exact gamS_lt_om hot hcb hμ hS k

theorem gamS_mono : ∀ k, gamS μ b seed k < gamS μ b seed (k + 1)
  | 0 => hS.lt_next
  | k + 1 => by
    show psi μ (fs b (gamS μ b seed k)) z < psi μ (fs b (gamS μ b seed (k + 1))) z
    rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, fs_mono hcb (gamS_mono k)⟩

theorem gamS_ge : ∀ k, psi μ z z ≤ gamS μ b seed (k + 1) := by
  intro k
  show psi μ z z ≤ psi μ (fs b (gamS μ b seed k)) z
  rw [le_iff]
  rcases (le_iff _ _).mp (z_le (fs b (gamS μ b seed k))) with h4 | h4
  · left; rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, h4⟩
  · right; rw [← h4]

theorem gamS_ot : ∀ k, isOT (gamS μ b seed k) = true := by
  have hbot : isOT b = true := isOT_arg hot
  have hcomp := comps_lt hot
  have hμot : isOT μ = true := isOT_cof_mu hbot hcb
  have haμ : a ≤ μ := le_of_not_gt hμ
  have hcompμ : ∀ g ∈ comps μ b, g < b := fun g hg => hcomp g (comps_mono haμ hg)
  intro k
  induction k with
  | zero => exact hS.ot
  | succ k ih =>
    show isOT (psi μ (fs b (gamS μ b seed k)) z) = true
    apply psi_ot_of_lhd hμot (isOT_fs hbot ⟨ih, by rw [hcb]; exact gamS_lt_om hot hcb hμ hS k⟩)
      (lhd_fs hbot (gamS_valid hot hcb hμ hS k)) hcompμ
    intro _ g hg
    cases k with
    | zero => exact hS.comps_a g (comps_mono haμ hg)
    | succ j =>
      have hss : lt μ μ = false := Bool.eq_false_iff.mpr (lt_irrefl' μ)
      have ih' := ih
      simp only [gamS] at hg ih'
      simp only [comps, hss, Bool.false_eq_true, if_false, List.mem_append,
        List.mem_cons] at hg
      have hmono : fs b (gamS μ b seed j) < fs b (gamS μ b seed (j + 1)) :=
        fs_mono hcb (gamS_mono hot hcb hμ hS j)
      rcases hg with (rfl | hg | hg) | hg
      · exact hmono
      · exact lt_trans (comps_lt ih' g hg) hmono
      · rw [comps_self_nil hμot] at hg; simp at hg
      · simp at hg

/-- The component condition along the chain (`Q` in Lemma 3.3). -/
theorem gamS_comps : ∀ k, ∀ g ∈ comps a (gamS μ b seed k), g < fs b (gamS μ b seed k) := by
  have hbot : isOT b = true := isOT_arg hot
  have hcomp := comps_lt hot
  intro k
  induction k with
  | zero => exact hS.comps_a
  | succ j ih =>
    intro g hg
    simp only [gamS] at hg
    simp only [comps, hμ, Bool.false_eq_true, if_false, List.mem_append, List.mem_cons] at hg
    have hmono : fs b (gamS μ b seed j) < fs b (gamS μ b seed (j + 1)) :=
      fs_mono hcb (gamS_mono hot hcb hμ hS j)
    have hV : Valid b (gamS μ b seed j) :=
      ⟨gamS_ot hot hcb hμ hS j, by rw [hcb]; exact gamS_lt_om hot hcb hμ hS j⟩
    rcases hg with (rfl | hg | hg) | hg
    · exact hmono
    · have hR := psi_ot_of_lhd (isOT_sub hot) (isOT_fs hbot hV)
        (lhd_fs hbot (gamS_valid hot hcb hμ hS j)) hcomp (fun _ => ih)
      exact lt_trans (comps_lt hR g hg) hmono
    · have hF5 := gamS_ge hot hcb hμ hS j
      have hF1 := gamS_lt_om hot hcb hμ hS (j + 1)
      have hgb : g ∈ comps a b := comps_mu hbot hcb hF5 hF1
        (le_of_lt (fs_lt (gamS_valid hot hcb hμ hS (j + 1)))) (le_refl b) hμ g hg
      have hgb' := hcomp g hgb
      by_contra hcon
      have hgy : g ∈ comps a g := comps_mu hbot hcb hF5 hF1
        (le_of_not_gt hcon) (le_of_lt hgb') hμ g hg
      exact Nat.lt_irrefl _ (size_comps hgy)
    · simp at hg

/-- **The diagonal node with a seeded index is standard.** -/
theorem isOT_diag_seed (m : Nat) : isOT (psi a (fs b (gamS μ b seed m)) z) = true := by
  have hbot : isOT b = true := isOT_arg hot
  have hV : Valid b (gamS μ b seed m) :=
    ⟨gamS_ot hot hcb hμ hS m, by rw [hcb]; exact gamS_lt_om hot hcb hμ hS m⟩
  exact psi_ot_of_lhd (isOT_sub hot) (isOT_fs hbot hV) (lhd_fs hbot (gamS_valid hot hcb hμ hS m))
    (comps_lt hot) (fun _ => gamS_comps hot hcb hμ hS m)

end chain

end Ytosk
