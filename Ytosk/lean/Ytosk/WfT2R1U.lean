/-
Path-level readers for the widened frame-shape residual.  These are the
FrameShapeXU counterparts of the path transfer lemmas in WfT2R1.
-/
import Ytosk.WfT2X7U
import Ytosk.WfT2R1

namespace Ytosk

open T Classical WfAbsW

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- Transfer `PathLvAll` across a frame in `FrameShapeXU`. -/
theorem pathLv_of_shapeXRU {M N : Mat} {ρ σ : Valn}
    (hC : Cons M ρ) (hCN : Cons N σ) {c : Nat}
    (hS : ∀ k, par N 0 c = some k → FrameShapeXU M N ρ σ k)
    (hup : ∀ k u, par N 0 c = some k → PathLvAll N σ k u → PathLvAll M ρ k u) :
    ∀ u, PathLvAll N σ c u → PathLvAll M ρ c u := by
  intro u h
  have hpar : ∀ {k : Nat} {Lc R : List Nat}, CL N k = Lc ++ c :: R → par N 0 c = some k := by
    intro k Lc R hcl
    exact (mem_children_iff.mp (cl_mem_children (show c ∈ CL N k by rw [hcl]; simp))).2
  cases h with
  | top hcl hsy ht =>
    obtain ⟨y', hclM, hv, hLc, hy', ht'⟩ :=
      WfT2X.rw_frame_of_shapeXU hC hCN (hS _ (hpar hcl)) hcl hsy ht
    rw [← hv]
    exact PathLvAll.top hclM hy' ht'
  | step hcl hsy ht hk =>
    obtain ⟨y', hclM, hv, hLc, hy', ht'⟩ :=
      WfT2X.rw_frame_of_shapeXU hC hCN (hS _ (hpar hcl)) hcl hsy ht
    exact PathLvAll.step hclM hy' ht' (hup _ u (hpar hcl) hk)

/-- `pathLvAll_pre_t2XR` with `FrameShapeXU` at non-seed columns. -/
theorem pathLvAll_pre_t2XRU {M N : Mat} {ρ σ : Valn} {r L : Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hGN : Good3 N σ)
    (hshape : ∀ k, k < r + L → ¬ T2SeedCol M r L k → FrameShapeXU M N ρ σ k)
    (hSP : ∀ p, T2Seed M r L p → ∀ (Lc : List Nat) (c : Nat) (R : List Nat),
      CL N p = Lc ++ c :: R → c < r + L →
      (∀ q, par M 0 (r + L) = some q → c ≠ q) → ∀ s y, σ.o c = psi s y z →
      (lt (spArg (σ.v p) z (sumN (Lc.map σ.o))) y = true ∧
        lt (psi (σ.v p) z z) (psi s y z) = true) →
      ∃ (Lc' R' : List Nat) (yM : T), CL M p = Lc' ++ c :: R' ∧ σ.v p = ρ.v p ∧
        Lc'.map ρ.o = Lc.map σ.o ∧ ρ.o c = psi s yM z ∧ y ≤ yM ∧
        (lt (spArg (ρ.v p) z (sumN (Lc'.map ρ.o))) yM = true ∧
          lt (psi (ρ.v p) z z) (psi s yM z) = true))
    (hqc : ∀ q, par M 0 (r + L) = some q → q ≠ r → ∀ c ∈ CL N q, ¬ c < r + L) :
    ∀ c u, PathLvAll N σ c u → c < r + L →
      (∀ q, par M 0 (r + L) = some q → q ≠ r → c ≠ q) → PathLvAll M ρ c u := by
  have hframe : ∀ k (Lc : List Nat) c (R : List Nat) s y,
      CL N k = Lc ++ c :: R → σ.o c = psi s y z →
      (lt (spArg (σ.v k) z (sumN (Lc.map σ.o))) y = true ∧
        lt (psi (σ.v k) z z) (psi s y z) = true) →
      c < r + L → (∀ q, par M 0 (r + L) = some q → q ≠ r → c ≠ q) →
      (∀ q, par M 0 (r + L) = some q → q ≠ r → k ≠ q) ∧
      ∃ (Lc' R' : List Nat) (yM : T), CL M k = Lc' ++ c :: R' ∧ σ.v k = ρ.v k ∧
        ρ.o c = psi s yM z ∧
        (lt (spArg (ρ.v k) z (sumN (Lc'.map ρ.o))) yM = true ∧
          lt (psi (ρ.v k) z z) (psi s yM z) = true) := by
    intro k Lc c R s y hcl hsy ht hcx hcq
    have hcCL : c ∈ CL N k := by rw [hcl]; simp
    have hkc := (mem_children (cl_mem_children hcCL)).1
    have hkq : ∀ q, par M 0 (r + L) = some q → q ≠ r → k ≠ q := by
      intro q hq hqr hkq
      subst hkq
      exact hqc k hq hqr c hcCL hcx
    refine ⟨hkq, ?_⟩
    by_cases hsc : T2SeedCol M r L k
    · rcases hsc with hsd | ⟨q, hq, hqr, hkq'⟩
      · obtain ⟨Lc', R', yM, h1, h2, _, h4, _, h6⟩ :=
          hSP k hsd Lc c R hcl hcx
            (fun q hq => by
              by_cases hqr : q = r
              · intro hcq'
                subst hcq'
                rcases hsd with ⟨_, hkr⟩ | ⟨q', hq', hq'r, _⟩
                · omega
                · rw [hq] at hq'
                  cases hq'
                  exact absurd hqr hq'r
              · exact hcq q hq hqr) s y hsy ht
        exact ⟨Lc', R', yM, h1, h2, h4, h6⟩
      · exact absurd hkq' (hkq q hq hqr)
    · obtain ⟨Lc', R', yM, h1, h2, _, h4, _, h6⟩ :=
        WfT2X.frame_of_shapeXU hC hG hCN hGN (hshape k (by omega) hsc) hcl hsy ht
      exact ⟨Lc', R', yM, h1, h2, h4, h6⟩
  intro c u hp
  induction hp with
  | @top k c Lc R s y hcl hsy ht =>
    intro hcx hcq
    obtain ⟨_, Lc', R', yM, h1, h2, h4, h6⟩ := hframe k Lc c R s y hcl hsy ht hcx hcq
    rw [h2]
    exact PathLvAll.top h1 h4 h6
  | @step k c Lc R s y u hcl hsy ht _ ih =>
    intro hcx hcq
    obtain ⟨hkq, Lc', R', yM, h1, _, h4, h6⟩ := hframe k Lc c R s y hcl hsy ht hcx hcq
    have hkc := (mem_children (cl_mem_children (show c ∈ CL N k by rw [hcl]; simp))).1
    exact PathLvAll.step h1 h4 h6 (ih (by omega) hkq)

end Ytosk
