/-
HsubAttempt.lean — psiI-specific pivot (team-lead).  Test whether the psiI graft
`hsub` closes WITHOUT the general SubstFree, using the cross-level (m<u) structure.

hsub : ∀ X ∈ W 0, based X → (2,1,1) :: shiftr01 3 0 X ∈ W 3.

REDUCTION (mechanical): (2,1,1)::shiftr01 3 0 X = shiftr01 2 0 ((0,1,1)::shiftr01 1 0 X),
so by W_shift hsub ⟸  N' := (0,1,1) :: shiftr01 1 0 X ∈ W 3.  N' is a based tower
`(0,v,z)::R` with v=1,z=1 (head level 3) and R = shiftr01 1 0 X (argOK free: row0≥1),
R ∈ W 0.  Question: does the tower revive at cross-level (m<3)?
-/
import Wtower2
import Final

namespace TRIO
namespace HsubAttempt

open Wset Three

/-- Mechanical reduction: hsub ⟸ the based tower `(0,1,1)::shiftr01 1 0 X ∈ W 3`. -/
theorem hsub_of_tower
    (htw : ∀ X : TrioSeq, X ∈ W 0 → based X →
      (((0, 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 X) ∈ W 3) :
    ∀ X : TrioSeq, X ∈ W 0 → based X →
      (((2, 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 3 0 X) ∈ W 3 := by
  intro X hX hbX
  have hadd : shiftr01 2 0 (shiftr01 1 0 X) = shiftr01 3 0 X := by
    unfold shiftr01; rw [List.map_map]
    apply List.map_congr_left
    intro p _
    simp only [Function.comp_def]
  have h := W_shift (htw X hX hbX) 2
  rw [shiftr01_cons, hadd] at h
  simpa using h

/-- R = shiftr01 1 0 X is argOK for any X (row 0 ≥ 1). -/
theorem argOK_shift1 (X : TrioSeq) : argOK (shiftr01 1 0 X) := by
  intro p hp
  rw [mem_shiftr01] at hp
  obtain ⟨q, -, rfl⟩ := hp
  simp

/-- Probe: A2' induction on X ∈ W 0 for the tower property.  trace_state the
three Aop cases (clause 3 is vacuous at stage 0). -/
theorem tower_of_W0_probe : ∀ X : TrioSeq, X ∈ W 0 →
    (((0, 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 X) ∈ W 3 := by
  have hsub : W 0 ⊆ {X : TrioSeq | (((0, 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 X) ∈ W 3} := by
    refine A2' ?_
    intro X hA
    rcases hA with ⟨hl, hlev⟩ | hop | ⟨m, hm, _, _⟩
    · -- clause 1: |X| ≤ 1, lev X 0 = 0
      show (((0, 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 X) ∈ W 3
      trace_state
      sorry
    · -- clause 2
      show (((0, 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 X) ∈ W 3
      set R : TrioSeq := shiftr01 1 0 X with hR
      have haR : argOK R := argOK_shift1 X
      by_cases hRnil : R = []
      · rw [hRnil]; exact singleton_mem_W (by omega)
      · refine mem_of_oper_mem (fun k hk => ?_)
        by_cases hpar : hasParent R (srow R (R.length - 1)) (R.length - 1)
        · -- MIRROR: oper_cons_nat + oper_shiftr01 + IH
          rw [oper_cons_nat haR hRnil hpar, hR, oper_shiftr01]
          exact hop k hk
        · -- non-parented: split by lev of the trailing
          by_cases hlev0 : lev R (R.length - 1) = 0
          · -- FLAT: srow = 0, oper_cons_succ → k copies of (0,1,1)::R.dropLast
            have he12 : entry R 1 (R.length - 1) = 0 ∧ entry R 2 (R.length - 1) = 0 := by
              unfold lev at hlev0; omega
            have hsrow0 : srow R (R.length - 1) = 0 := by
              unfold srow; rw [he12.1, he12.2]; simp
            rw [hsrow0] at hpar
            rw [oper_cons_succ haR hRnil hlev0 hpar]
            -- residual: (List.range k).flatMap (fun _ => (0,1,1)::R.dropLast) ∈ W 3
            trace_state
            sorry
          · -- HIGH ORPHAN: does the head revive it (tower/O2)?
            trace_state
            sorry
    · exact absurd hm (Nat.not_lt_zero m)
  intro X hX; exact hsub hX

end HsubAttempt
end TRIO
