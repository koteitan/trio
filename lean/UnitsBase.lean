/-
UnitsBase.lean — the units-base / flat self-concat lemma for GT_nest/childLoad
(SHORT + OPER-no-parent).  Target (team-lead): GTC CQ v ([(1,v+1,1)]ⁿ), the
repeated bare far-word head (one word, orphan-trailing).  GTC_far_CQ is n=1.
-/
import HbB
import GzD

namespace TRIO
namespace UnitsBase

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GzD GzH GzJ HbB

theorem units_base (v : ℕ) : ∀ n,
    GTC CQ v ((List.range n).flatMap (fun _ => [((1, v + 1, 1) : ℕ × ℕ × ℕ)])) := by
  intro n
  induction n with
  | zero =>
      simp only [List.range_zero, List.flatMap_nil]
      intro L hC hL hB
      exact BwT_snocz hL hB
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      -- Goal: GTC CQ v ([(1,v+1,1)]ⁿ ++ [(1,v+1,1)])  from  ih : GTC CQ v ([(1,v+1,1)]ⁿ).
      -- The appended (1,v+1,1) is a far-word HEAD col (row2=1), orphan-trailing.
      -- ROUTE (for Climb / BwT layer): unfold GTC→BwT; from ih get
      --   hBK : BwT v (L ++ [Kⁿ]); at level u the K^{n+1} word wraps to
      --   rcol 0 u ([(1,u+1,1)]^{n+1}) = (1,u+1,1)::[(2,u+1,1)]^{n+1}, i.e. the Kⁿ word
      --   plus ONE extra trailing (2,u+1,1). Need Wstarv-snoc of that orphan:
      --     A ∈ Wstarv u → A ++ [(2,u+1,1)] ∈ Wstarv u   (via mem_of_oper_mem + Pred).
      -- ⚠ SUBTLETY: whether the trailing (2,u+1,1) is a genuine orphan (Preds) is
      --   context-dependent — the root (0,u,0) has row2=0 and could be a row-2 parent
      --   (nextrel2) of it, so this needs the BwT/Wstarv-level parent analysis
      --   (Climb's Pred/GoodChtX layer), not a purely local step.
      sorry

end UnitsBase
end TRIO
