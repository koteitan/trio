/-
ChildLoad.lean: keystone `childLoad` = far-word 頭の子として Wg-load を吊るす GTC。
`gt_trc4` の GT_nest sorry を閉じる。A2g'(Y 帰納)。base=GTC_far_CQ、flat根=GTC_oper(tie-tower)、
tie根=再帰 GTC_tie。GTC_oper/GTC_tie は hCK 不要なので CQ 文脈で通る。
-/
import HbB
import GzD

namespace TRIO
namespace ChildLoad

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GzD GzH GzJ HbB

/-- content = (1,v+1,1) :: shiftr01 2 0 Y。 -/
theorem childLoad (v : ℕ) : ∀ Y : TrioSeq, Y ∈ Wg (2 * (v + 1)) → based Y →
    GTC CQ v (((1, v + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 Y) := by
  have key : Wg (2 * (v + 1)) ⊆ {Y : TrioSeq | Y ∈ Wg (2 * (v + 1)) ∧
      (based Y → GTC CQ v (((1, v + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 Y))} := by
    refine A2g' ?_
    intro Y hA
    have hYW : Y ∈ Wg (2 * (v + 1)) := A1g_intro (Aopg_mono_X hA (fun U hU => hU.1))
    refine ⟨hYW, ?_⟩
    intro hb
    have hb0 : entry Y 0 0 = 0 := hb
    set K : TrioSeq := [((1, v + 1, 1) : ℕ × ℕ × ℕ)] with hKdef
    have hKrow0 : ∀ y ∈ K, 1 ≤ y.1 := by
      intro y hy; rw [hKdef] at hy; simp at hy; rw [hy]
    have econt : (((1, v + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 Y) = K ++ shiftr01 2 0 Y := by
      rw [hKdef]; rfl
    rw [econt]
    by_cases hYnil : Y = []
    · -- base: Y = [] → content = fwTop v [] → GTC_far_CQ
      subst hYnil
      have e : K ++ shiftr01 2 0 ([] : TrioSeq) = fwTop v [] := by
        rw [hKdef]; simp [shiftr01, fwTop, unitsC]
      rw [e]; exact GTC_far_CQ v
    · rcases hA with ⟨hl, hw0⟩ | ⟨hnat, hop⟩ | ⟨m', hm, hd, h20, hgr⟩
      · -- short: Y ≠ [] ∧ |Y| ≤ 1 → single based col (0,0,0)-ish; flat sub-case (tie-tower)
        sorry
      · -- oper: Y natDom
        by_cases hp : 2 ≤ Y.length ∧ hasParent Y (srow Y (Y.length - 1)) (Y.length - 1)
        · obtain ⟨hlen2, hp⟩ := hp
          have hlenC : 2 ≤ (K ++ shiftr01 2 0 Y).length := by rw [hKdef]; simp [shiftr01]; omega
          have hidx : (K ++ shiftr01 2 0 Y).length - 1 = K.length + (Y.length - 1) := by
            rw [hKdef]; simp [shiftr01]; omega
          have hpC : hasParent (K ++ shiftr01 2 0 Y)
              (srow (K ++ shiftr01 2 0 Y) ((K ++ shiftr01 2 0 Y).length - 1))
              ((K ++ shiftr01 2 0 Y).length - 1) := by
            rw [hidx, srow_append_right, srow_shiftr01]
            exact hasParent_append_right_of K (shiftr01 2 0 Y) (hasParent_shiftr01.mpr hp)
          refine GTC_oper hlenC hpC (fun n hn => ?_)
          rw [oper_shift K Y 2 n hlen2 hp]
          exact ((hop n hn).2 (based_oper hn hb))
        · sorry
      · -- graft: last col row2=0, srow=1 (row1=j∈[1,v+1]). j≤v → GTC_orph (needs row1-noCross
        -- lemma to avoid rsum); j=v+1 → recursive GTC_tie (GoodChtX_deep core). Both open.
        sorry
  intro Y hY hb
  exact (key hY).2 hb

end ChildLoad
end TRIO
