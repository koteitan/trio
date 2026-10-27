/-
The final summand is never absorbed by addition. The final nonzero input of
sumN therefore keeps all its components, without a decreasing-list premise.
-/
import Ytosk.V3Subst
import Ytosk.V3Chg

namespace Ytosk.SumComps
open T

/-- Addition preserves every component of the right operand. -/
theorem mem_add_right {u A B g : T} (hg : g ∈ comps u B) : g ∈ comps u (add A B) := by
  obtain ⟨P, hP, _⟩ := add_eq_app_prefix A B
  rw [hP, comps_app]
  exact List.mem_append_right _ hg

/-- The final input's components survive sumN, with no ordering assumption. -/
theorem mem_sumN_snoc {l : List T} {t u g : T}
    (hl : ∀ q ∈ l, isOT q = true) (ht : isOT t = true) (hg : g ∈ comps u t) :
    g ∈ comps u (sumN (l ++ [t])) := by
  rw [sumN_snoc, sf_ot (isOT_add (isOT_sumN l hl) ht)]
  exact mem_add_right hg

/-- Appending zero inputs does not change a standard sum. -/
theorem sumN_append_zeros {l r : List T}
    (hl : ∀ q ∈ l, isOT q = true) (hr : ∀ q ∈ r, q = z) :
    sumN (l ++ r) = sumN l := by
  have key : ∀ r : List T, (∀ q ∈ r, q = z) → ∀ a, isOT a = true →
      r.foldl (fun a b => sf (add a b)) a = a := by
    intro r
    induction r with
    | nil => intro _ a _; rfl
    | cons t r ih =>
      intro hz a ha
      rw [List.foldl_cons, hz t (by simp), add_z_right, sf_ot ha]
      exact ih (fun q hq => hz q (by simp [hq])) a ha
  simpa only [sumN, List.foldl_append] using key r hr (sumN l) (isOT_sumN l hl)

/-- The last nonzero input, even before trailing zeros, retains its components. -/
theorem mem_sumN_last_nonzero {l r : List T} {t u g : T}
    (hl : ∀ q ∈ l, isOT q = true) (ht : isOT t = true)
    (hr : ∀ q ∈ r, q = z) (hg : g ∈ comps u t) :
    g ∈ comps u (sumN (l ++ t :: r)) := by
  have hs : ∀ q ∈ l ++ [t], isOT q = true := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hl q hq
    · simp only [List.mem_singleton] at hq
      subst q
      exact ht
  have he : l ++ t :: r = (l ++ [t]) ++ r := by simp
  rw [he, sumN_append_zeros hs hr]
  exact mem_sumN_snoc hl ht hg

end Ytosk.SumComps
