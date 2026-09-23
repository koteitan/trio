/-
GTnestAttempt.lean — attack psiI's keystone GT_nest (team-lead: THE main event).
green ⟹ gt_trc4 ⟹ Cpsi.psiI_mem ⟹ psiI ∈ W 0 unconditionally.

GT_nest {v W} (hW : GT (v+1) W) (hWr : ∀y∈W, 1≤y.1) : GT v (rcol 0 v W).
rcol 0 v W = (1,v+1,1) :: shiftr01 1 0 W.  Unfold to the core word-membership goal.
-/
import GxN
import GzD
import GxV

namespace TRIO
namespace GTnestAttempt

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GzD GxV

theorem GT_nest_probe {v : ℕ} {W : TrioSeq} (hW : GT (v + 1) W) (hWr : ∀ y ∈ W, 1 ≤ y.1) :
    GT v (rcol 0 v W) := by
  intro L hL hB
  intro u hu
  rw [List.map_append, List.map_cons, List.map_nil, rword_append, rword_singleton,
    mlift_rcol hWr, show v + (u - v) = u from by omega]
  have hA : rword 0 u (L.map (fun X => mlift X v (u - v))) ∈ Wstarv u := hB u hu
  -- ★ CLEAN RESIDUAL (single sorry): Wstarv u is closed under appending the
  -- NESTED far-word of W.  With A := rword 0 u (L.map …) ∈ Wstarv u and
  -- V := mlift W v (u-v) (= W lifted to level u):
  --   ⊢ A ++ rcol 0 u (rcol 0 u V) ∈ Wstarv u
  -- This is the GT-append closure for the far-word content rcol 0 v W; it is NOT
  -- peelable by existing lemmas (BwT_farwords appends a word via ITS GT — here we
  -- are proving that GT).  Closing it needs the far-word TOWER construction
  -- (à la GzD.tower_Wg / GxK.GT_tie: oper_zcone/farword_oper + tow + Wg), with the
  -- inner content W fed through hW : GT (v+1) W.  That is the psiI keystone core.
  sorry

end GTnestAttempt
end TRIO
