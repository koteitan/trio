/-
UnitsBaseTower.lean — units_base : ∀n v, GTC CQ v ([(1,v+1,1)]ⁿ), for SHORT+OPER of childLoad.
Route (CORRECTED): NOT BwT_append_words (Kⁿ is bare-head, not a WordsG far-word — GT v Kⁿ is
false context-free, cone fails at root). Instead: direct Wg via oper_zcone on the last (2,u+1,1),
with the flat expansion terms closed by the IH (units_base(n-1) at levels u+j). n-induction (∀v).
Mirrors GTC_far_CQ (HbB:170) generalized from 1 to n far-heads.
-/
import HbB
import GzD

namespace TRIO
namespace UnitsBaseTower

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GzD GzH GzJ HbB

/-- The n-far-head word. -/
noncomputable def fh (v : ℕ) : ℕ → TrioSeq
  | 0 => []
  | n + 1 => ((1, v + 1, 1) : ℕ × ℕ × ℕ) :: fh v n

theorem fh_eq_flatMap (v n : ℕ) :
    fh v n = (List.range n).flatMap (fun _ => [((1, v + 1, 1) : ℕ × ℕ × ℕ)]) := by
  induction n with
  | zero => simp [fh]
  | succ n ih => rw [List.range_succ_eq_map, List.flatMap_cons]; simp [fh, ih, List.flatMap_map]

/-- units_base: n-far-head word is GTC in CQ, for all levels v. -/
theorem units_base : ∀ (n v : ℕ), GTC CQ v (fh v n) := by
  intro n
  induction n with
  | zero =>
      intro v L hC hL hB
      simpa [fh] using BwT_snocz hL hB
  | succ n ih =>
      intro v L hC hL hB u hu _ a ha
      obtain ⟨bs, uss, hR, hNT, rfl⟩ := hC
      trace_state
      sorry

end UnitsBaseTower
end TRIO
