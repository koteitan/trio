/-
ChildLoadClose.lean: ChildLoad.childLoad の 3 sorry を閉じる（scratch, Prover の ChildLoad.lean と非衝突）。
GTC 層のラッパー HdR.gtc_orph / gtc_tie / gtc_flat / gtc_oper を使う。
green になれば ChildLoad.childLoad に統合し GT_nest → psiI ∈ W 0 が無条件。
-/
import HbB
import GzD
import HdR

namespace TRIO
namespace ChildLoadClose

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GzD GzH GzJ HbB HdR

/-- head [(1,v+1,1)] は PathCone v 2。 -/
theorem pathCone_head (v : ℕ) : PathCone v 2 ([((1, v + 1, 1) : ℕ × ℕ × ℕ)]) := by
  intro y hy _ _
  simp only [List.length_singleton] at hy
  obtain rfl : y = 0 := by omega
  show v < entry ([((1, v + 1, 1) : ℕ × ℕ × ℕ)]) 1 0
  show v < v + 1; omega

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
    have econt : (((1, v + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 Y) = K ++ shiftr01 2 0 Y := by
      rw [hKdef]; rfl
    rw [econt]
    by_cases hYnil : Y = []
    · subst hYnil
      have e : K ++ shiftr01 2 0 ([] : TrioSeq) = fwTop v [] := by
        rw [hKdef]; simp [shiftr01, fwTop, unitsC]
      rw [e]; exact GTC_far_CQ v
    · rcases hA with ⟨hl, hw0⟩ | ⟨hnat, hop⟩ | ⟨m', hm, hd, h20, hgr⟩
      · -- SHORT
        sorry
      · -- OPER
        sorry
      · -- GRAFT: Y = U ++ [(h,j,0)], last col z=0 (h20), lev=2j=m'+1, m'<2(v+1) → j≤v+1
        have hYne : Y ≠ [] := hYnil
        have hYl : 0 < Y.length := List.length_pos_iff.mpr hYne
        have hjeq : 2 * entry Y 1 (Y.length - 1) = m' + 1 := by
          have h := hd.1; unfold lev at h; rw [h20] at h; omega
        set jj : ℕ := entry Y 1 (Y.length - 1) with hjj
        set hh : ℕ := entry Y 0 (Y.length - 1) with hhh
        have hj2 : 2 * jj = m' + 1 := hjeq
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
        -- content = K ++ shiftr01 2 0 (Y.dropLast ++ [(hh,jj,0)])
        have hsrY : srow Y (Y.length - 1) = 1 := by
          unfold srow; rw [h20, if_neg (by omega)]
          rw [← hjj, if_pos (by omega)]
        rw [hlast, shiftr01_append0]
        have esh : shiftr01 2 0 ([((hh, jj, 0) : ℕ × ℕ × ℕ)]) = [((hh + 2, jj, 0) : ℕ × ℕ × ℕ)] := by
          simp [shiftr01]
        rw [esh, ← List.append_assoc]
        set Ko : TrioSeq := K ++ shiftr01 2 0 (Y.dropLast) with hKo
        -- goal: GTC CQ v (Ko ++ [(hh+2, jj, 0)])
        rcases Nat.lt_or_ge jj (v + 1) with hjlt | hjge
        · -- jj ≤ v: GTC_orph
          have hjv : jj ≤ v := by omega
          have hcontent : Ko ++ [((hh + 2, jj, 0) : ℕ × ℕ × ℕ)] = K ++ shiftr01 2 0 Y := by
            rw [hKo, List.append_assoc]; congr 1
            conv_rhs => rw [hlast, shiftr01_append0, esh]
          refine GTC_orph hj1 hjv ?_ (fun z hz' hbz => ?_)
          · -- hnp: row1-noCross via noParent_ctx
            rw [hcontent]
            have hlenidx : (K ++ shiftr01 2 0 Y).length - 1
                = K.length + ((shiftr01 2 0 Y).length - 1) := by
              rw [List.length_append, shiftr01_length, hKdef]; simp; omega
            rw [hlenidx]
            refine noParent_ctx (A := K) (B := shiftr01 2 0 Y)
              (b := (shiftr01 2 0 Y).length - 1) (j := jj) ?_ ?_ ?_ ?_
            · rw [shiftr01_length]; omega
            · intro k hk _
              rw [hKdef] at hk; simp only [List.length_singleton] at hk
              obtain rfl : k = 0 := by omega
              show jj ≤ entry K 1 0; rw [hKdef]; show jj ≤ v + 1; omega
            · rw [entry1_shiftr01, shiftr01_length, ← hjj]
            · rw [hasParent_shiftr01, shiftr01_length]
              have := hd.2; rw [hsrY] at this; exact this
          · -- hzK from hgr
            sorry
        · -- jj = v+1: GTC_tie
          sorry
  intro Y hY hb
  exact (key hY).2 hb

end ChildLoadClose
end TRIO
