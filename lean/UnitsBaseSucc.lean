/-
UnitsBaseSucc.lean — units_base succ (multi-head far-word tower) in own scratch
(avoids collision with Climb's UnitsBaseTower). Helpers copied (green there).
Goal: GTC CQ v (fh v (n+1)) from IH GTC CQ v (fh v n).
Route: at level u the appended (n+1)-head word wraps to (1,u+1,1)::[(2,u+1,1)]ⁿ⁺¹;
oper_zcone on the last (2,u+1,1); flat terms via IH.
-/
import HbB
import GzD
import GxV

namespace TRIO
namespace UnitsBaseSucc

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxV GzD GzH GzJ HbB

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

theorem mlift_fh (v n d : ℕ) : mlift (fh v n) v d = fh (v + d) n := by
  rw [fh_replicate, fh_replicate, mlift, List.length_replicate]
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, List.length_replicate]
  · intro j hj1 _
    rw [List.length_map, List.length_range] at hj1
    have hj : j < n := hj1
    rw [List.getElem_map, List.getElem_range, List.getElem_replicate,
      entry_repl0 v n j hj, entry_repl1 v n j hj]
    have e2 : entry (List.replicate n ((1, v + 1, 1) : ℕ × ℕ × ℕ)) 2 j = 1 := by
      simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
        (show j < (List.replicate n ((1, v + 1, 1) : ℕ × ℕ × ℕ)).length by
          rw [List.length_replicate]; exact hj)]
    rw [e2]
    have hcone : coneV (List.replicate n ((1, v + 1, 1) : ℕ × ℕ × ℕ)) v j := by
      intro y hy
      have hyj : y = j := by
        rcases Relation.ReflTransGen.cases_tail hy with h1 | ⟨z, _, hzj⟩
        · exact h1.symm
        · exfalso
          obtain ⟨hzl, hjl, hzlt, hent, -⟩ := hzj
          rw [List.length_replicate] at hzl hjl
          rw [entry_repl0 v n z hzl, entry_repl0 v n j hjl] at hent; omega
      rw [hyj, entry_repl1 v n j hj]; omega
    rw [if_pos hcone]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    show v + 1 + d = v + d + 1; omega

/-- Probe: units_base succ, goal after simplification. -/
theorem units_base_succ (n : ℕ) (ih : ∀ v, GTC CQ v (fh v n)) :
    ∀ v, GTC CQ v (fh v (n + 1)) := by
  intro v L hC hL hB u hu _ a ha
  obtain ⟨bs, uss, hR, hNT, rfl⟩ := hC
  -- simplify the appended word
  rw [List.map_append, List.map_cons, List.map_nil, rword_append, rword_singleton,
    mlift_fh, show v + (u - v) = u from by omega]
  -- Goal: (0,u,0) :: (P ++ rcol 0 u (fh u (n+1))) ∈ Wg a,  P = rword 0 u (CQ-prefix lifted).
  -- rcol 0 u (fh u (n+1)) = (1,u+1,1) :: [(2,u+1,1)]ⁿ⁺¹  (shiftr01_fh).
  -- ROUTE (mirrors GTC_far_CQ HbB:170, generalized 1→(n+1) far-heads):
  --   A1g_intro (natDom via zcone_natDom + oper via oper_zcone on the LAST (2,u+1,1));
  --   oper_zcone peels it → the flat expansion is the n-head tower, closed by IH
  --   (units_base n) + the n-head generalization of farWAQ_flat / topCQ_Wg / towWAQ.
  -- GAP: farWAQ_P/farWAQ_flat/topCQ_Wg (HbB) are stated for the SINGLE far-head
  --   (fwTop v []); the (n+1)-head [(2,u+1,1)]ⁿ⁺¹ needs their n-parametrized versions
  --   (towWAQ already carries a tower-height m — the connection fh(n) ↔ towWAQ@m is
  --   the far-word-CQ machinery). That generalization is Climb's HbB layer.
  sorry

end UnitsBaseSucc
end TRIO
