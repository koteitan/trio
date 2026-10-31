/-
**WfQnA19 (2026-11-01): a `TPLoSX` witness at a failing comparison is a bad call** (half of `TPLoSXIn`).
`win_of_fail`: if `ψ(A[ζ]) < ψ(s + 1)`, `¬ V < s` and `V < A` (`A[ζ]` a single term), the leading summand `q`
of `V` lies in the window `A[ζ] ≤ q < A`.  `witness_bad`: hence the witness `i` of `TPLoSX` (bad shape,
`W = A`, `¬ V < s`) is in `BadSet` at `ζ`, given rows 1, 2 nonzero and `hVlt`.  The other half of `TPLoSXIn`
(the closure climbs from `m = P₀ i` to the ancestor `c`) is left open.
-/
import Ytosk.WfQnA18

namespace Ytosk.WfQnA19
open T Ytosk Ytosk.WfQnE3 Ytosk.WfBad Ytosk.WfQnE2

theorem win_of_fail {V A Az s : T} (hAz : ∃ a b, Az = psi a b z) (hVlt : V < A) (hns : ¬ V < s)
    (hlt : psi Az z z < psi (succ s) z z) : ∃ q ∈ summands V, q < A ∧ ¬ q < Az := by
  obtain ⟨a', b', rfl⟩ := hAz
  have h1 : psi a' b' z < succ s := by
    rcases psi_lt_psi_z_iff.mp hlt with h | ⟨_, h⟩
    · exact h
    · exact absurd h (T.not_lt_z _)
  have h2 : psi a' b' z ≤ s := lt_succ_iff.mp h1
  have h3 : psi a' b' z ≤ V := le_trans h2 (le_of_not_gt hns)
  cases V with
  | z => exact absurd (lt_of_lt_of_le (T.z_lt_psi _ _ _) h3) (T.not_lt_z _)
  | psi a b c =>
    refine ⟨psi a b z, by simp [summands], ?_, ?_⟩
    · have hle : psi a b z ≤ psi a b c := by
        rcases c with _ | ⟨c1, c2, c3⟩
        · exact le_refl _
        · exact le_of_lt (by rw [T.psi_lt_psi]; simp [T.z_lt_psi])
      exact lt_of_le_of_lt hle hVlt
    · intro hq
      have : psi a b c < psi a' b' z := psi_lt_psi_z_iff.mpr (psi_lt_psi_z_iff.mp hq)
      exact absurd (lt_of_lt_of_le this h3) (lt_irrefl _)

theorem witness_bad {M : Mat} {x r i : Nat} {ρ : Valn} {ζ a s : T} (hi : i < x) (hdi : DepX M x false i)
    (hbs : BadShape1 M i) (h1i : entry M 1 i ≠ 0) (h2i : entry M 2 i ≠ 0) (ha : a = bumpW M ρ i)
    (hW : bumpW M ρ i = ρ.o r) (hns : ¬ vOpt ρ (par M 1 i) < s)
    (hlt : psi (fsD a ζ) z z < psi (succ s) z z) (hVlt : vOpt ρ (par M 1 i) < ρ.o r)
    (hAz : ∃ a b, fsD (ρ.o r) ζ = psi a b z) : BadSet M x ρ r ζ i := by
  subst ha
  rw [hW] at hlt
  obtain ⟨q, hq, hqA, hqz⟩ := win_of_fail hAz hVlt hns hlt
  exact ⟨hi, hdi, hbs, h1i, h2i, hW, q, hq, by rw [hW]; exact hqA, by rw [hW]; exact hqz⟩

end Ytosk.WfQnA19
