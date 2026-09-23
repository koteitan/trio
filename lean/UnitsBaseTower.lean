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

theorem shiftr01_fh (v n : ℕ) :
    shiftr01 1 0 (fh v n) = List.replicate n ((2, v + 1, 1) : ℕ × ℕ × ℕ) := by
  induction n with
  | zero => simp [fh, shiftr01]
  | succ n ih => simp only [fh, shiftr01, List.map_cons, List.replicate_succ]; rw [← shiftr01, ih]

theorem fh_row0 (v n : ℕ) : ∀ y ∈ fh v n, 1 ≤ y.1 := by
  induction n with
  | zero => intro y hy; simp [fh] at hy
  | succ n ih =>
      intro y hy; simp only [fh, List.mem_cons] at hy
      rcases hy with rfl | hy
      · omega
      · exact ih y hy

theorem fh_replicate (v n : ℕ) : fh v n = List.replicate n ((1, v + 1, 1) : ℕ × ℕ × ℕ) := by
  induction n with
  | zero => simp [fh]
  | succ n ih => rw [fh, ih, List.replicate_succ]

theorem entry_repl0 (v n j : ℕ) (hj : j < n) :
    entry (List.replicate n ((1, v + 1, 1) : ℕ × ℕ × ℕ)) 0 j = 1 := by
  simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
    (show j < (List.replicate n ((1, v + 1, 1) : ℕ × ℕ × ℕ)).length by
      rw [List.length_replicate]; exact hj)]

theorem entry_repl1 (v n j : ℕ) (hj : j < n) :
    entry (List.replicate n ((1, v + 1, 1) : ℕ × ℕ × ℕ)) 1 j = v + 1 := by
  simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
    (show j < (List.replicate n ((1, v + 1, 1) : ℕ × ℕ × ℕ)).length by
      rw [List.length_replicate]; exact hj)]

theorem entry_repl2 (v n j : ℕ) (hj : j < n) :
    entry (List.replicate n ((1, v + 1, 1) : ℕ × ℕ × ℕ)) 2 j = 1 := by
  simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
    (show j < (List.replicate n ((1, v + 1, 1) : ℕ × ℕ × ℕ)).length by
      rw [List.length_replicate]; exact hj)]

theorem coneV_repl (v n j : ℕ) (hj : j < n) :
    coneV (List.replicate n ((1, v + 1, 1) : ℕ × ℕ × ℕ)) v j := by
  intro y hy
  have hyj : y = j := by
    rcases Relation.ReflTransGen.cases_tail hy with h1 | ⟨z, _, hzj⟩
    · exact h1.symm
    · exfalso
      obtain ⟨hzl, hjl, hzlt, hent, -⟩ := hzj
      rw [List.length_replicate] at hzl hjl
      rw [entry_repl0 v n z hzl, entry_repl0 v n j hjl] at hent
      omega
  rw [hyj, entry_repl1 v n j hj]; omega

theorem mlift_fh (v n d : ℕ) : mlift (fh v n) v d = fh (v + d) n := by
  rw [fh_replicate, fh_replicate, mlift, List.length_replicate]
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, List.length_replicate]
  · intro j hj1 _
    rw [List.length_map, List.length_range] at hj1
    rw [List.getElem_map, List.getElem_range, List.getElem_replicate,
      entry_repl0 v n j hj1, entry_repl1 v n j hj1, entry_repl2 v n j hj1,
      if_pos (coneV_repl v n j hj1)]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    show v + 1 + d = v + d + 1; omega

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
