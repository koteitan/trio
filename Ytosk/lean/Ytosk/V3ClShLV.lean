/-
Partial results for ClShL with VDomF and the first conjunct of KAG.

The two unguarded / VDomF-only counterexamples live in V3ClShL.lean.
This file contains ONLY the guarded task's proved helper lemmas.

KA is exactly the requested condition at levels u <= V (unshifted old
components of a); it is not replaced by the stronger SubstDom.1.
low_components discharges introduced components and the ordinary unchanged
component bounds. Moving images, general interval persistence through sh,
and the levels above V remain unresolved. There is no full clShL theorem.
-/
import Ytosk.V3ShadowL
import Ytosk.V3T2VRAK

namespace Ytosk.ClShLGuarded

open T

/-- The old-component hypothesis requested for the guarded ClShL. -/
def KA (V V' a : T) : Prop :=
  ∀ u, ¬ lt V u = true → ∀ d ∈ comps u a,
    d ≤ psi (shf V V' a) z z ∨ ∃ d' ∈ comps u (shf V V' a), d ≤ d'

/-- The interval alternative, separated from the two component bounds. -/
def Persistent (u g B A : T) : Prop :=
  ∀ c, B < c → c ≤ A → ∃ d ∈ Gc u c, g ≤ d

/-- The frame's summand bound puts the shifted state above Omega_{f(a)}. -/
theorem omega_le_state {V V' a B s y : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hVa : V ≤ a) (hB : isOT B = true) (hBz : B ≠ z)
    (hBs : ∀ q ∈ summands B, psi s y z ≤ q)
    (hBV : ∀ q ∈ summands B, V < lev q)
    (ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true) :
    psi (shf V V' a) z z ≤ sh V V' B := by
  have has : a ≤ s := le_of_trig ht.2
  exact om_shf_le_sh hV hV' (le_of_lt hVV) ha hVa hB hBz hBV
    (fun q hq => le_trans has (lev_le_of_le (hBs q hq)))

/-- VDomF discharges every component introduced from V', at all levels. -/
theorem introduced_bound {V V' a B u g : T} (hVD : VDomF V V' a)
    (hOm : psi (shf V V' a) z z ≤ sh V V' B)
    (hu : ¬ lt (shf V V' a) u = true) (hg : g ∈ comps u V') :
    g ≤ sh V V' B ∨ ∃ d ∈ comps u (shf V V' a), g ≤ d := by
  rcases hVD u hu g hg with h | h
  · exact Or.inl (le_trans h hOm)
  · exact Or.inr h

/-- KA discharges the unchanged old components of a at levels at most V. -/
theorem retained_index_bound {V V' a B u g : T} (hKA : KA V V' a)
    (hOm : psi (shf V V' a) z z ≤ sh V V' B)
    (hu : ¬ lt V u = true) (hg : g ∈ comps u a) :
    g ≤ sh V V' B ∨ ∃ d ∈ comps u (shf V V' a), g ≤ d := by
  rcases hKA u hu g hg with h | h
  · exact Or.inl (le_trans h hOm)
  · exact Or.inr h

/-- For an unchanged component of B the only remaining case is its old
interval alternative; neither the state bound nor old-index domination remains. -/
theorem retained_component {V V' a B A u g : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (hVa : V ≤ a) (hB : isOT B = true) (hKA : KA V V' a)
    (hOm : psi (shf V V' a) z z ≤ sh V V' B)
    (hcl : ClosedL a B A) (hu : ¬ lt V u = true) (hg : g ∈ comps u B) :
    g ≤ sh V V' B ∨ (∃ d ∈ comps u (shf V V' a), g ≤ d) ∨ Persistent u g B A := by
  have hua : ¬ lt a u = true := not_lt.mpr (le_trans (not_lt.mp hu) hVa)
  rcases hcl u hua g hg with h | ⟨d, hd, hgd⟩ | h
  · exact Or.inl (le_trans h (le_sh hV hV' (le_of_lt hVV) hB))
  · rcases retained_index_bound hKA hOm hu hd with h | ⟨d', hd', hdd'⟩
    · exact Or.inl (le_trans hgd h)
    · exact Or.inr (Or.inl ⟨d', hd', le_trans hgd hdd'⟩)
  · exact Or.inr (Or.inr h)

/-- A precise low-level reduction of guarded ClShL. The unsolved cases
are moving images and the transport of an old interval-persistent component.
This is a reduction, not a proof of the full ClShL statement. -/
theorem low_components {V V' a B A u g : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hVa : V ≤ a) (hB : isOT B = true)
    (hVD : VDomF V V' a) (hKA : KA V V' a)
    (hOm : psi (shf V V' a) z z ≤ sh V V' B)
    (hcl : ClosedL a B A) (hu : ¬ lt V u = true) (hg : g ∈ comps u (sh V V' B)) :
    g ≤ sh V V' B ∨ (∃ d ∈ comps u (shf V V' a), g ≤ d) ∨
      (∃ d ∈ compsAN V u (size B) B, g = sh V V' d) ∨ Persistent u g B A := by
  have hufa : ¬ lt (shf V V' a) u = true :=
    not_lt.mpr (le_trans (not_lt.mp hu) (le_trans hVa (le_shf_self hV hV' (le_of_lt hVV) ha hVa)))
  rcases comps_sh_levA V V' (not_lt.mp hu) (size B) B g (Nat.le_refl _) hg with
      ⟨d, hd, he⟩ | ⟨d, hd, he⟩ | ⟨q, hq, hgq⟩
  · exact Or.inr (Or.inr (Or.inl ⟨d, hd, he⟩))
  · subst g
    rcases retained_component hV hV' hVV hVa hB hKA hOm hcl hu hd with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  · rcases introduced_bound hVD hOm hufa (comps_of_mem_summands hq hgq) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- Every term between two terms with the same leading index retains
that index, even when the intermediate term is not a standard term. -/
theorem persistent_of_shared_level {u g p x r y t : T}
    (hup : u ≤ p) (hg : g ∈ comps u p) :
    Persistent u g (psi p x r) (psi p y t) := by
  intro c hc1 hc2
  cases c with
  | z => exact False.elim (T.not_lt_z _ hc1)
  | psi q e f =>
    have hpq : p ≤ q := by simpa only [lev] using lev_le_of_le (le_of_lt hc1)
    have hqp : q ≤ p := by simpa only [lev] using lev_le_of_le hc2
    have hqp' : q = p := le_antisymm hqp hpq
    subst q
    refine ⟨g, List.mem_cons_of_mem _ ?_, le_refl _⟩
    exact comps_psi_mem_of (not_lt.mpr hup) (Or.inr (Or.inr (Or.inl hg)))

#print axioms low_components
#print axioms persistent_of_shared_level

end Ytosk.ClShLGuarded
