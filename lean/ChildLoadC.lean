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
      · -- GRAFT (j≤v: GTC_orph at level u; j=v+1: gtc_tie, hload from hgr all-levels)
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
