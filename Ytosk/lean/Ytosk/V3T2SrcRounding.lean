/- A principal increment below the last summand cannot jump a cutoff.
This separates the unchanged prefix from the changed final child. -/
import Ytosk.V3T2SrcUpgraded

namespace Ytosk.T2SrcRounding
open T

/-- Round up a smaller prefix by at most the cutoff's last summand. -/
theorem add_below_last {s y : T} : ∀ P H : T, isOT P = true → H < P →
    psi s y z ≤ last P → add H (psi s y z) ≤ P
  | z, H, _, h, _ => False.elim (not_lt_z H h)
  | psi a b c, z, hP, _, hD => by
    rw [add_z_left]
    exact le_trans hD (le_trans (last_le_head hP) (head_le_self _))
  | psi a b c, psi d e f, hP, hlt, hD => by
    have hhead : psi d e z ≤ psi a b z := by simpa only [head] using head_le_of_lt hlt
    have hDhead : psi s y z ≤ psi a b z := le_trans hD (last_le_head hP)
    by_cases hdh : psi d e z < psi a b z
    · rcases (le_iff _ _).mp hDhead with hDh | hDeq
      · have hh : head (add (psi d e f) (psi s y z)) < psi a b z := by
          by_cases hDS : psi s y z ≤ psi d e z
          · rw [head_add_le (by simpa only [head] using hDS) (by simp)]
            exact hdh
          · rw [add_eq_right_of_head_lt (by simpa only [head] using (lt_of_not_ge hDS))]
            exact hDh
        exact le_of_lt (lt_of_head_lt hh)
      · rw [add_eq_right_of_head_lt (by simpa only [head, hDeq] using hdh), hDeq]
        exact head_le_self (psi a b c)
    · have he := le_antisymm hhead (le_of_not_gt hdh)
      simp only [psi.injEq, and_true] at he
      obtain ⟨rfl, rfl⟩ := he
      have hfc : f < c := by
        rw [T.psi_lt_psi] at hlt
        rcases hlt with h | ⟨_, h⟩ | ⟨_, _, h⟩
        · exact False.elim (lt_irrefl d h)
        · exact False.elim (lt_irrefl e h)
        · exact h
      have hcne : c ≠ z := by intro he; rw [he] at hfc; exact not_lt_z f hfc
      have hl : last (psi d e c) = last c := by
        cases c with
        | z => exact False.elim (hcne rfl)
        | psi _ _ _ => rfl
      rw [hl] at hD
      have ht := add_below_last c f (isOT_rest hP) hfc hD
      rw [add_psi_psi, if_neg (not_lt_of_ge hDhead)]
      exact psi_le_psi_rest ht

/-- If a final child increment cannot itself jump P, crossing P forces
the unchanged prefix already to reach P. The new child is nonzero, so
its new sum is strictly above P. -/
theorem replacement_above_cutoff {H P s y s' y' : T}
    (hP : isOT P = true) (hD : psi s y z ≤ last P)
    (hOld : P < add H (psi s y z)) : P < add H (psi s' y' z) := by
  have hPH : P ≤ H := by
    by_contra hn
    have he := add_below_last P H hP (lt_of_not_ge hn) hD
    exact not_lt_of_ge he hOld
  exact lt_of_le_of_lt hPH (lt_add_principal s' y' H)


/-- Between two principal increments, a cutoff must contain a summand
between them. The unchanged prefix cannot create another crossing. -/
theorem summand_in_replacement_window {s y s' y' : T} : ∀ H P : T,
    ¬ P < add H (psi s' y' z) → P < add H (psi s y z) →
    ∃ r ∈ summands P, ¬ r < psi s' y' z ∧ r < psi s y z
  | H, P, hn, ho => by
    have base {X : T} (hno : ¬ X < psi s' y' z) (hyes : X < psi s y z) :
        ∃ r ∈ summands X, ¬ r < psi s' y' z ∧ r < psi s y z := by
      have hxne : X ≠ z := by intro he; rw [he] at hno; exact hno (z_lt_psi _ _ _)
      refine ⟨head X, head_mem_summands hxne, ?_, ?_⟩
      · intro h
        exact hno (lt_of_head_lt h)
      · rcases head_lt_of_lt_principal hyes with hz | hh
        · exact False.elim (hxne hz)
        · exact hh
    cases H with
    | z => simpa only [add_z_left] using base hn ho
    | psi a b c =>
      by_cases hh : psi a b z < psi s y z
      · rw [add_psi_psi, if_pos hh] at ho
        apply base ?_ ho
        intro hp
        exact hn (lt_of_lt_of_le hp (le_add_single (psi a b c) ⟨s', y', rfl⟩))
      · have hnew : psi s' y' z < psi s y z := by
          by_contra h
          exact hn (lt_of_lt_of_le ho (add_le_add_left _ (le_of_not_gt h)))
        have hnnew : ¬ psi a b z < psi s' y' z := by
          intro h
          exact hh (lt_trans h hnew)
        rw [add_psi_psi, if_neg hh] at ho
        rw [add_psi_psi, if_neg hnnew] at hn
        cases P with
        | z => exact False.elim (hn (z_lt_psi _ _ _))
        | psi d e f =>
          have hle : psi d e z ≤ psi a b z := by simpa only [head] using head_le_of_lt ho
          have hge : psi a b z ≤ psi d e z := by
            by_contra h
            exact hn (lt_of_head_lt (by simpa only [head] using (lt_of_not_ge h)))
          have he := le_antisymm hle hge
          simp only [psi.injEq, and_true] at he
          obtain ⟨rfl, rfl⟩ := he
          have hft : f < add c (psi s y z) := by
            rw [T.psi_lt_psi] at ho
            rcases ho with h | ⟨_, h⟩ | ⟨_, _, h⟩
            · exact False.elim (lt_irrefl d h)
            · exact False.elim (lt_irrefl e h)
            · exact h
          have hfn : ¬ f < add c (psi s' y' z) := by
            intro h
            exact hn (by rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, h⟩))
          obtain ⟨r, hr, h1, h2⟩ := summand_in_replacement_window c f hfn hft
          exact ⟨r, by simp only [summands, List.mem_cons]; exact Or.inr hr, h1, h2⟩
  termination_by H _ _ _ => sizeOf H

/-- Order reflection for normalized omega powers. -/
theorem omega_lt_reflect {P Q : T} (hP : isOT P = true) (hQ : isOT Q = true)
    (h : omega P < omega Q) : P < Q := by
  by_contra hn
  exact not_lt_of_ge (omega_le_omega hQ hP (le_of_not_gt hn)) h

/-- A cutoff omega power is preserved across the final-child replacement
when the old child is below the last summand of its exponent. -/
theorem omega_replacement_above_cutoff {H P s y s' y' : T}
    (hH : isOT H = true) (hP : isOT P = true)
    (hD : isOT (psi s y z) = true) (hD' : isOT (psi s' y' z) = true)
    (hLast : psi s y z ≤ last P)
    (hOld : omega P < omega (add H (psi s y z))) :
    omega P < omega (add H (psi s' y' z)) := by
  have hp := omega_lt_reflect hP (isOT_add hH hD) hOld
  exact omega_lt_omega hP (isOT_add hH hD') (replacement_above_cutoff hP hLast hp)


/-- No crossing at any summand means no crossing after adding a common
prefix. This is a pointwise cutoff criterion, with no matrix hypothesis. -/
theorem replacement_above_of_summands {H P s y s' y' : T}
    (hCross : ∀ r ∈ summands P, r < psi s y z → r < psi s' y' z)
    (hOld : P < add H (psi s y z)) : P < add H (psi s' y' z) := by
  by_contra hn
  obtain ⟨r, hr, hnew, hold⟩ := summand_in_replacement_window H P hn hOld
  exact hnew (hCross r hr hold)

/-- Lift a pointwise principal cutoff comparison through an outer omega.
Its exponent is arbitrary; it need not be just one target bump branch. -/
theorem outer_omega_replacement {P Q G G' : T}
    (hP : isOT P = true) (hQ : isOT Q = true)
    (hG : isOT G = true) (hG' : isOT G' = true)
    (hCross : ∀ r ∈ summands P, r < omega G → r < omega G')
    (hOld : omega P < omega (add Q (omega G))) :
    omega P < omega (add Q (omega G')) := by
  have hp := omega_lt_reflect hP (isOT_add hQ (isOT_omega hG)) hOld
  obtain ⟨s, y, hg⟩ := omega_psi_form G
  obtain ⟨s', y', hg'⟩ := omega_psi_form G'
  have hnew : P < add Q (omega G') := by
    simp only [hg, hg'] at hCross hp ⊢
    exact replacement_above_of_summands hCross hp
  exact omega_lt_omega hP (isOT_add hQ (isOT_omega hG')) hnew

/-- A direct last bump leaf may add one after the changed old branch.
The boundary exponent then gives Lhd by the consecutive-omega lemma;
all strictly smaller exponents are handled by the same cutoff comparison. -/
theorem outer_omega_replacement_succ {P Q G G' : T}
    (hP : isOT P = true) (hQ : isOT Q = true)
    (hG : isOT G = true) (hG' : isOT G' = true)
    (hCross : ∀ r ∈ summands P, r < omega G → r < omega G')
    (hOld : omega P < omega (succ (add Q (omega G)))) :
    omega P < omega (add Q (omega G')) ∨
      Lhd z (omega P) (omega (succ (add Q (omega G)))) := by
  have hPQ := omega_lt_reflect hP (isOT_succ (isOT_add hQ (isOT_omega hG))) hOld
  have hle := lt_succ_iff.mp hPQ
  rcases (le_iff _ _).mp hle with hlt | he
  · exact Or.inl (outer_omega_replacement hP hQ hG hG' hCross
      (omega_lt_omega hP (isOT_add hQ (isOT_omega hG)) hlt))
  · right
    rw [he]
    exact lhd_omega_succ (isOT_add hQ (isOT_omega hG))


/-- It suffices to check the last exponent summand only for cutoff terms
that would otherwise sit between the two inner omega powers. -/
theorem crossing_closed_by_last_exponents {P H s y s' y' : T}
    (hH : isOT H = true) (hD : isOT (psi s y z) = true)
    (hD' : isOT (psi s' y' z) = true)
    (hCut : ∀ r ∈ summands P,
      ¬ r < omega (add H (psi s' y' z)) → r < omega (add H (psi s y z)) →
      ∃ R, isOT R = true ∧ r = omega R ∧ psi s y z ≤ last R) :
    ∀ r ∈ summands P, r < omega (add H (psi s y z)) →
      r < omega (add H (psi s' y' z)) := by
  intro r hr hold
  by_contra hn
  obtain ⟨R, hR, he, hl⟩ := hCut r hr hn hold
  rw [he] at hn hold
  exact hn (omega_replacement_above_cutoff hH hR hD hD' hl hold)

end Ytosk.T2SrcRounding
