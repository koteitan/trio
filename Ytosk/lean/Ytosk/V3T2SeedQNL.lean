/-
**3 行・t = 2・q ≠ r: 種 r = P_0(q) の ◁（SeedL）を M と M.take x だけの性質から。**

s′ = v_N(q) = v(r) + ω^{1+Σ}（vq_eq_gexp、どの段でも同じ）、v_N(x′) = v(r) + last(s′) = s′。
X_{n−1} = B + Ω_t なら X_n = step_a(B, s′, H(s′, σ_{a,s′}(X_{n−1}))) = B + Ω_{σ(t)}（`qn_step`）。
基点 X_1（M.take x での r の引数）= B + Ω_{t_1} と、t の列の条件は残り `T2SeedQNRes`（M と M.take x だけ）。
-/
import Ytosk.V3T2SeedQN

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- The iteration `t_{k+1} = f(t_k)` of `f = σ_{a, s′}` on subscripts. -/
def tqN (a s' t1 : T) : Nat → T
  | 0 => t1
  | k + 1 => shf a s' (tqN a s' t1 k)

/-- `v_N(q)` in terms of `M` (`vq_eq_gexp`). -/
def qnS (M : Mat) (ρ : Valn) (r L q : Nat) : T :=
  add (ρ.v r) (omega (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q))))

/-- **One level of the `q ≠ r` seed**: `B + Ω_t ↦ B + Ω_{f(t)}`. -/
theorem qn_step {a B s' t : T} (hs' : isOT s' = true) (has : a < s') (hσB : sh a s' B = B)
    (hBc : ∀ g ∈ summands B, ¬ g < psi (succ s') z z) (hat : a < t)
    (hts : ¬ shf a s' t < succ s') :
    step a B s' (step s' z s' (sh a s' (app B (psi t z z))) z) z = app B (psi (shf a s' t) z z) := by
  rw [sh_app, hσB, sh_psi_gt hat, sh_z]
  have hne : app B (psi (shf a s' t) (sh a s' z) z) ≠ z := by
    intro h; cases B with
    | z => simp at h
    | psi _ _ _ => simp at h
  have hhigh : ∀ g ∈ summands (app B (psi (shf a s' t) (sh a s' z) z)), ¬ g < psi (succ s') z z := by
    intro g hg
    rw [summands_app] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hBc g hg
    · simp [summands] at hg; rw [hg]
      intro hlt
      rw [psi_lt_psi_z_iff] at hlt
      rcases hlt with h | ⟨_, h⟩
      · exact hts h
      · exact T.not_lt_z _ h
  rw [sh_z] at hne hhigh
  have hzlt : z < app B (psi (shf a s' t) z z) := by
    cases h : app B (psi (shf a s' t) z z) with
    | z => exact absurd h hne
    | psi _ _ _ => exact T.z_lt_psi _ _ _
  -- the frame of `q`
  have hin : step s' z s' (app B (psi (shf a s' t) z z)) z = app B (psi (shf a s' t) z z) := by
    unfold step
    rw [if_pos ⟨hzlt, psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hzlt⟩)⟩]
    exact H_of_high hs' hhigh
  rw [hin]
  -- the frame of `r`
  unfold step
  rw [if_pos ⟨lt_app_of (by simp), psi_lt_psi_z_iff.mpr (Or.inl has)⟩]
  exact H_of_high hs' hhigh

end Ytosk
