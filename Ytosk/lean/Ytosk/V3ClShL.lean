/-
Counterexample to the proposed pure ordinal ClShL lemma.
The interval alternative in ClosedL does not make unrestricted substitution safe.
All the proposed frame hypotheses hold, but the substituted state has an
uncontrolled component even at the upper endpoint of the new interval.
-/
import Ytosk.V3ShadowL
import Ytosk.V3T2SeedSVCl

namespace Ytosk.ClShLCounterexample

open T

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private def numeral : Nat → T
  | 0 => z
  | n + 1 => psi z z (numeral n)

def V : T := psi (numeral 2) z z
def V' : T := app (psi (numeral 3) z z)
  (psi one (psi one (psi z (psi (psi (numeral 5) z z) z z) z) z) z)
def a : T := app V (psi one V z)
def b : T := succ a
def s : T := a
def B : T := psi b (psi (succ V) z z) z
def y : T := psi b (psi b z z) z

def g : T := psi (psi (numeral 5) z z) z z
def c : T := sh V V' y

def af : T := app (psi (numeral 3) z z) (psi one V z)
def bf : T := succ af
def Bf : T := psi bf (psi (succ V') z z) z
def yf : T := psi bf (psi bf z z) z

theorem subst_a : shf V V' a = af := by
  simp [shf, a, V, V', af, sh, sub, add, lt, app, numeral, one]

theorem subst_s : shf V V' s = af := subst_a

theorem subst_B : sh V V' B = Bf := by
  simp [B, b, a, V, V', Bf, bf, af, sh, sub, add, lt, app, succ, numeral, one]

theorem subst_y : sh V V' y = yf := by
  simp [y, b, a, V, V', yf, bf, af, sh, sub, add, lt, app, succ, numeral, one]

private theorem comps_succ_sub' (u t d : T) (h : d ∈ comps u (succ t)) :
    d = z ∨ d ∈ comps u t := by
  rw [succ, comps_app] at h
  rcases List.mem_append.mp h with h | h
  · exact Or.inr h
  · left
    simp only [one, comps] at h
    split at h <;> simp_all

private theorem comps_single_sub {u t x d : T}
    (h : d ∈ comps u (psi t x z)) :
    d = x ∨ d ∈ comps u x ∨ d ∈ comps u t := by
  by_cases htu : lt t u = true
  · simp [comps, htu] at h
  · simpa [comps, htu] using h

private theorem v_components {u d : T} (h : d ∈ comps u V) : d ∈ comps u a := by
  rw [a, comps_app]
  exact List.mem_append_left _ h

/-- The original state satisfies even the stronger ClosedA. -/
theorem old_closedA : ClosedA a B := by
  intro u _ d hd
  change d ∈ comps u (psi (succ a) (psi (succ V) z z) z) at hd
  rcases comps_single_sub hd with rfl | hd | hd
  · left; decide
  · rcases comps_single_sub hd with rfl | hd | hd
    · exact Or.inl (z_le _)
    · simp [comps] at hd
    · rcases comps_succ_sub' u V d hd with rfl | hd
      · exact Or.inl (z_le _)
      · exact Or.inr ⟨d, v_components hd, le_refl _⟩
  · rcases comps_succ_sub' u a d hd with rfl | hd
    · exact Or.inl (z_le _)
    · exact Or.inr ⟨d, hd, le_refl _⟩

/-- Every hypothesis of the proposed statement, with the exact original types. -/
structure Premises : Prop where
  hV : isOT V = true
  hV' : isOT V' = true
  hVV : V < V'
  ha : isOT a = true
  hVa : V ≤ a
  hB : isOT B = true
  hsy : isOT (psi s y z) = true
  hVs : V < s
  hBs : ∀ q ∈ summands B, psi s y z ≤ q
  hBV : ∀ q ∈ summands B, V < lev q
  ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true
  hhi : B < (split y (psi (succ s) z z)).1
  hnp : ¬ ∃ R, (split y (psi (succ s) z z)).1 = app B R
  hcl : ClosedL a B (H a (H s y))

theorem premises : Premises := by
  refine ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ?_, ?_, by decide, by decide, ?_, old_closedA.toL⟩
  · intro q hq
    have : q = B := by simpa [B, summands] using hq
    subst q
    decide
  · intro q hq
    have : q = B := by simpa [B, summands] using hq
    subst q
    decide
  · rintro ⟨R, hR⟩
    change psi b (psi b z z) z = psi b (psi (succ V) z z) R at hR
    have hne : psi b z z ≠ psi (succ V) z z := by decide
    exact hne (T.psi.inj hR).2.1

/-- The new state has the large component g at level zero. -/
theorem new_component : g ∈ comps z (sh V V' B) := by
  rw [subst_B]; decide

/-- Choosing c equal to the new upper endpoint defeats the interval escape. -/
theorem witness_bounds :
    sh V V' B < c ∧ c ≤ H (shf V V' a) (H (shf V V' s) (sh V V' y)) := by
  rw [c, subst_B, subst_y, subst_a, subst_s]; decide

theorem new_not_closedL :
    ¬ ClosedL (shf V V' a) (sh V V' B)
      (H (shf V V' a) (H (shf V V' s) (sh V V' y))) := by
  intro h
  rcases h z (T.not_lt_z _) g new_component with h | h | h
  · exact (show ¬ g ≤ sh V V' B by rw [subst_B]; decide) h
  · exact (show ¬ ∃ d ∈ comps z (shf V V' a), g ≤ d by rw [subst_a]; decide) h
  · exact (show ¬ ∃ d ∈ Gc z c, g ≤ d by rw [c, subst_y]; decide)
      (h c witness_bounds.1 witness_bounds.2)

/-- All premises hold and the requested conclusion fails. No extra hypotheses. -/
theorem counterexample : Premises ∧
    ¬ ClosedL (shf V V' a) (sh V V' B)
      (H (shf V V' a) (H (shf V V' s) (sh V V' y))) :=
  ⟨premises, new_not_closedL⟩

#print axioms counterexample

end Ytosk.ClShLCounterexample
