/-
ChildLoadC.lean — (B) GTallC-CQ refactor of childLoad: state at ALL levels u≥v so the
A2g' graft-closure (hgr) arrives at every level, satisfying gtc_tie's cross-level hload.
  childLoadC v : ∀Y∈Wg(2(v+1)) based, ∀u≥v, GTC CQ u ((1,u+1,1)::shiftr01 2 0 (mlift Y v (u-v)))
u=v gives childLoad (mlift_zero). GoodChtX_deep-style cross-level recursion.
-/
import HbB
import GzD
import HdR

namespace TRIO
namespace ChildLoadC

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GzD GzH GzJ HbB HdR

theorem childLoadC (v : ℕ) : ∀ Y : TrioSeq, Y ∈ Wg (2 * (v + 1)) → based Y →
    ∀ u, v ≤ u → GTC CQ u (((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 (mlift Y v (u - v))) := by
  have key : Wg (2 * (v + 1)) ⊆ {Y : TrioSeq | Y ∈ Wg (2 * (v + 1)) ∧
      (based Y → ∀ u, v ≤ u →
        GTC CQ u (((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 (mlift Y v (u - v))))} := by
    refine A2g' ?_
    intro Y hA
    have hYW : Y ∈ Wg (2 * (v + 1)) := A1g_intro (Aopg_mono_X hA (fun U hU => hU.1))
    refine ⟨hYW, ?_⟩
    intro hb u hu
    by_cases hYnil : Y = []
    · subst hYnil
      have e : ((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 (mlift ([] : TrioSeq) v (u - v))
          = fwTop u [] := by
        rw [mlift_nil]; simp [shiftr01, fwTop, unitsC]
      rw [e]; exact GTC_far_CQ u
    · rcases hA with ⟨hl, hw0⟩ | ⟨hnat, hop⟩ | ⟨m', hm, hd, h20, hgr⟩
      · -- SHORT (needs units_base at level u)
        sorry
      · -- OPER
        sorry
      · -- GRAFT
        have hYne : Y ≠ [] := hYnil
        have hYl : 0 < Y.length := List.length_pos_iff.mpr hYne
        have hjeq : 2 * entry Y 1 (Y.length - 1) = m' + 1 := by
          have h := hd.1; unfold lev at h; rw [h20] at h; omega
        set jj : ℕ := entry Y 1 (Y.length - 1) with hjj
        set hh : ℕ := entry Y 0 (Y.length - 1) with hhh
        have hj1 : 1 ≤ jj := by omega
        have hjv1 : jj ≤ v + 1 := by omega
        have hcol : Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) = ((hh, jj, 0) : ℕ × ℕ × ℕ) :=
          Prod.ext rfl (Prod.ext rfl h20)
        have hgl : Y.getLast hYne = ((hh, jj, 0) : ℕ × ℕ × ℕ) := by
          have h1 : Y.getLast hYne = Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) := by
            rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show Y.length - 1 < Y.length by omega)]
            rfl
          rw [h1, hcol]
        have hlast : Y = Y.dropLast ++ [((hh, jj, 0) : ℕ × ℕ × ℕ)] := by
          rw [← hgl]; exact (List.dropLast_append_getLast hYne).symm
        have hsrY : srow Y (Y.length - 1) = 1 := by
          unfold srow; rw [h20, if_neg (by omega), ← hjj, if_pos (by omega)]
        rcases Nat.lt_or_ge jj (v + 1) with hjlt | hjge
        · -- j ≤ v : GTC_orph at level u
          have hjv : jj ≤ v := by omega
          trace_state
          sorry
        · -- j = v+1 : gtc_tie at level u
          sorry
  intro Y hY hb u hu
  exact (key hY).2 hb u hu

/-- childLoad (level v) follows from childLoadC at u=v. -/
theorem childLoad (v : ℕ) : ∀ Y : TrioSeq, Y ∈ Wg (2 * (v + 1)) → based Y →
    GTC CQ v (((1, v + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 Y) := by
  intro Y hY hb
  have h := childLoadC v Y hY hb v le_rfl
  rwa [Nat.sub_self, mlift_zero] at h

end ChildLoadC
end TRIO
