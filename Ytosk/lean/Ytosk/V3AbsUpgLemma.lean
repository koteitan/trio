/-
**V3AbsUpgLemma (2026-11-01): discharging an allowance that is not the collapsing level.**

`WfAbsW.lhd_psi_dis` discharges the allowance `V` of `Lhd V b0 b` under `ψ_V`, i.e. only when the allowance is
the collapsing level.  In the six upgrade-shape frames of the absorption failures (tmp/claude/abs_slack.py: the bad
column `i` is not counted by `m = P₀ i = P₁ i`, the column `c = i − 1` upgrades to `i` and copies its value, and
the slack `Lhd_{v(m)}` of `c` is resolved at `p = P₀ c ≠ m`), the allowance `v(m)` differs from the level `v(p)`,
and `Lhd_{v(p)}` fails in 4 of the 6 frames.  What holds in all 6 is that every component of `v(m)` (at a level
`u ≤ v(p)`) is below the new argument of `o(p)`.

- `lhd_psi_disG`: `Lhd V b0 b` and every component of `V` at a level `u ≤ v` below `b0` give `ψ_v(b0) ◁ ψ_v(b)`.
- `o_frame_lhdVG`: `WfAbsW.o_frame_lhdV` with any allowance `V` on the last counted child `c`, given that every
  component of `V` at a level `u ≤ v(i)` is below `σ.o c`.
-/
import Ytosk.WfAbsWEta
import Ytosk.WfQrH6

namespace Ytosk.WfAbsW

open T

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **Collapse with an allowance below the new argument.** -/
theorem lhd_psi_disG {V v b0 b : T} (h : Lhd V b0 b)
    (hsm : ∀ u, ¬ lt v u = true → ∀ g ∈ comps u V, g ≤ b0) : Lhd z (psi v b0 z) (psi v b z) := by
  refine ⟨by rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, h.1⟩, fun u c h1 h2 => ?_⟩
  obtain ⟨c0, c1, rfl, hc1, hc2⟩ := between_psi h1 h2
  intro x hx
  have hsub : ∀ w ∈ comps u (psi v c0 z), w ∈ comps u (psi v c0 c1) := by
    intro w hw; simp only [comps, List.mem_append] at hw ⊢; left; simpa using hw
  rcases (le_iff _ _).mp hc1 with hc1 | rfl
  · simp only [comps, List.mem_append] at hx
    rcases hx with hx | hx
    · split at hx
      · simp at hx
      · rename_i hvu
        simp only [List.mem_cons, List.mem_append] at hx
        rcases hx with rfl | hx | hx
        · exact ⟨c0, List.mem_append_left _ (by simp [comps, hvu]), le_of_lt hc1⟩
        · obtain ⟨y, hy, hxy⟩ := h.2 u c0 hc1 hc2 x hx
          rcases List.mem_append.mp hy with hy | hy
          · exact ⟨y, List.mem_append_left _ (by simp [comps, hvu, hy]), hxy⟩
          · simp only [Gc, List.mem_cons] at hy
            rcases hy with rfl | hy
            · exact ⟨z, List.mem_append_right _ (by simp [Gc]), hxy⟩
            · exact ⟨c0, List.mem_append_left _ (by simp [comps, hvu]),
                le_trans hxy (le_trans (hsm u hvu y hy) (le_of_lt hc1))⟩
        · exact ⟨x, List.mem_append_left _ (by simp [comps, hvu, hx]), le_refl _⟩
    · simp at hx
  · exact ⟨x, List.mem_append_left _ (hsub x hx), le_refl _⟩

/-- **The parent `o` frame with a foreign allowance**: as `o_frame_lhdV`, with the last counted child `c` going
down by `Lhd V` for any `V` whose components at levels `u ≤ v(i)` are below the new `o(c)`. -/
theorem o_frame_lhdVG {M N : Mat} {ρ σ : Valn} {i c : Nat} {Lc : List Nat} {V : T}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hGN : GoodOT N σ)
    (hiM : i < M.length) (hiN : i < N.length) (hv : σ.v i = ρ.v i)
    (hclN : CL N i = Lc ++ [c]) (hclM : CL M i = Lc ++ [c])
    (hsame : ∀ d ∈ Lc, σ.o d = ρ.o d)
    (hl : Lhd V (σ.o c) (ρ.o c))
    (hsm : ∀ u, ¬ lt (ρ.v i) u = true → ∀ g ∈ comps u V, g ≤ σ.o c)
    (hs : ∃ s, ρ.o c = psi s z z) (hs' : ∃ s', σ.o c = psi s' z z)
    (hpN0 : ((CL N i).map σ.o).Pairwise (fun a b => b ≤ a)) :
    Lhd z (σ.o i) (ρ.o i) := by
  have hcM : c < M.length := (mem_children (cl_mem_children (show c ∈ CL M i by rw [hclM]; simp))).2
  have hvot : isOT (ρ.v i) = true := hG.ot_v i hiM
  obtain ⟨s, hsy⟩ := hs
  obtain ⟨s', hs'y'⟩ := hs'
  obtain ⟨hsM, hpM⟩ := cl_vals hC hG hiM
  have hformM := o_last_form hC hiM hvot hclM (fun d hd => single_o hC hG
    (mem_children (cl_mem_children hd)).2) hpM hsy
  have hformN := o_last_form hCN hiN (by rw [hv]; exact hvot) hclN (fun d hd => single_oT hCN hGN
    (mem_children (cl_mem_children hd)).2) hpN0 hs'y'
  have hLm : Lc.map σ.o = Lc.map ρ.o := List.map_congr_left hsame
  rw [hLm, hv] at hformN
  rw [hformN, hformM, step_y0, step_y0]
  set a := ρ.v i
  set B := spArg a z (sumN (Lc.map ρ.o)) with hB
  rw [hclM] at hsM hpM
  have hpM' := hpM
  simp only [List.map_append, List.map_cons, List.map_nil] at hpM'
  have hsL : ∀ t ∈ Lc.map ρ.o, Single t := fun t ht =>
    hsM t (by simp only [List.map_append]; exact List.mem_append_left _ ht)
  have hp1 := List.pairwise_append.mp hpM'
  have hLs := sumN_dec (Lc.map ρ.o) hsL hp1.1
  have hBc : ∀ q ∈ summands B, psi s z z ≤ q := by
    intro q hq
    apply spArg_summands_ge ⟨s, z, rfl⟩ (sumN (Lc.map ρ.o)) z hLs.1
    · rw [hLs.2]; intro q hq; rw [← hsy]; exact hp1.2.2 q hq _ (by simp)
    · simp [summands]
    · exact hq
  have hlt' : psi s' z z < psi s z z := by rw [← hsy, ← hs'y']; exact hl.1
  rw [add_eq_app_of_ge ⟨s, z, rfl⟩ B hBc,
    add_eq_app_of_ge ⟨s', z, rfl⟩ B (fun q hq => le_trans (le_of_lt hlt') (hBc q hq))]
  have hle : psi s' z z ≤ app B (psi s' z z) :=
    WfQrH6.le_app_Q (fun q hq => le_trans (le_of_lt hlt') (hBc q hq))
  rw [hsy, hs'y'] at hl
  rw [hs'y'] at hsm
  exact lhd_psi_disG (lhd_app B hl) (fun u hu g hg => le_trans (hsm u hu g hg) hle)

end Ytosk.WfAbsW
