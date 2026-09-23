/-
Clause2Reduce.lean — Clause2 (Aop branch 2) partial reduction.

Clause2 : ∀ S, (∀ n≥1, SubstProp (S⟦n⟧)) → SubstProp S.
Datum hIH : ∀ n≥1, SubstProp (S⟦n⟧).  The p-analysis of the substitution
R = S.take p ++ C ++ D (D = S.drop (p+1)) has the same trichotomy as Clause3.

`clause2_mirror` (GREEN): the MIRROR case — D has ≥2 columns and its trailing
column has a parent inside D — closes directly from the datum: `oper_append_inner`
mirrors `oper` across the substitution, so `R⟦n⟧ = subst (S⟦n⟧) p C`, and hIH n
at position p with block C gives `R⟦n⟧ ∈ Wself` for every n, then
`mem_of_oper_mem`.  (SubstProp inlined identically to L7Subst.)
-/
import Wtower2
import Final

namespace TRIO
namespace Clause2Reduce

open Wset Three

def SubstProp (S : TrioSeq) : Prop :=
  ∀ (p : ℕ) (C : TrioSeq), p < S.length → C ≠ [] → C ∈ Wself →
    (S.take p ++ C ++ S.drop (p + 1)) ∈ Wself

/-- **Clause2 MIRROR case** — closed from the datum `hIH`. -/
theorem clause2_mirror (S C : TrioSeq) (p : ℕ)
    (hIH : ∀ n : ℕ, 1 ≤ n → SubstProp (S⟦n⟧))
    (hp : p < S.length) (hCne : C ≠ []) (hCW : C ∈ Wself)
    (hDlen : 2 ≤ (S.drop (p + 1)).length)
    (hDp : hasParent (S.drop (p + 1))
      (srow (S.drop (p + 1)) ((S.drop (p + 1)).length - 1))
      ((S.drop (p + 1)).length - 1)) :
    (S.take p ++ C ++ S.drop (p + 1)) ∈ Wself := by
  set D : TrioSeq := S.drop (p + 1) with hD
  set AC : TrioSeq := S.take p ++ C with hAC
  have hDne : D ≠ [] := by
    intro h; rw [h] at hDlen; simp at hDlen
  have hDL : D.length - 1 ≠ 0 := by omega
  have hp1S : p + 1 ≤ S.length := by omega
  have htk : (S.take (p + 1)).length = p + 1 := by
    rw [List.length_take]; omega
  have hACpos : 0 < AC.length := by
    rw [hAC, List.length_append]; have := List.length_pos_iff.mpr hCne; omega
  -- S = S.take (p+1) ++ D
  have hSsplit : S.take (p + 1) ++ D = S := List.take_append_drop _ _
  -- expansions mirror
  have hOpS : ∀ n, S⟦n⟧ = S.take (p + 1) ++ D⟦n⟧ := by
    intro n; conv_lhs => rw [← hSsplit]
    exact oper_append_inner n hDne hDL hDp
  have hOpR : ∀ n, (AC ++ D)⟦n⟧ = AC ++ D⟦n⟧ := fun n =>
    oper_append_inner n hDne hDL hDp
  -- lev of R⟦n⟧ equals lev of R (shared AC prefix)
  set R : TrioSeq := AC ++ D with hRdef
  show R ∈ W (lev R 0)
  refine mem_of_oper_mem (fun n hn => ?_)
  -- R⟦n⟧ = AC ++ D⟦n⟧
  rw [hOpR n]
  -- apply datum at S⟦n⟧
  have hSnlen : p < (S⟦n⟧).length := by
    rw [hOpS n, List.length_append, htk]; omega
  have hstep := hIH n hn p C hSnlen hCne hCW
  have htake' : (S⟦n⟧).take p = S.take p := by
    rw [hOpS n, List.take_append_of_le_length (by rw [htk]; omega),
      List.take_take, show min p (p + 1) = p from by omega]
  have hdrop' : (S⟦n⟧).drop (p + 1) = D⟦n⟧ := by
    rw [hOpS n, List.drop_append_of_le_length (le_of_eq htk.symm),
      List.drop_eq_nil_of_le (le_of_eq htk), List.nil_append]
  rw [htake', hdrop'] at hstep
  -- hstep : (S.take p ++ C) ++ D⟦n⟧ ∈ Wself ;  fold to AC
  rw [← hAC] at hstep
  -- convert Wself (= W (lev · 0)) to W (lev R 0)
  have hlev : lev (AC ++ D⟦n⟧) 0 = lev R 0 := by
    have h0 : ∀ i, entry (AC ++ D⟦n⟧) i 0 = entry R i 0 := by
      intro i
      rw [entry_append_left _ _ hACpos, hRdef, entry_append_left _ _ hACpos]
    unfold lev; rw [h0 1, h0 2]
  have hmem : AC ++ D⟦n⟧ ∈ W (lev (AC ++ D⟦n⟧) 0) := hstep
  rwa [hlev] at hmem

end Clause2Reduce
end TRIO
