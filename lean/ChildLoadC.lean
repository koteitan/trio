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

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GzD GzH GzJ HbB HdR

/-- row1-noCross (level u). Inlined from Graft61C (verified green). -/
theorem row1_noCross {u j : ℕ} (hj : j ≤ u) {Y' : TrioSeq} (hY'ne : Y' ≠ [])
    (hj_eq : entry Y' 1 (Y'.length - 1) = j)
    (hY'orph : ¬ hasParent Y' 1 (Y'.length - 1)) :
    ¬ hasParent (((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 Y') 1
      ((((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 Y').length - 1) := by
  have hY'len : 0 < Y'.length := List.length_pos_iff.mpr hY'ne
  set A : TrioSeq := [((1, u + 1, 1) : ℕ × ℕ × ℕ)] with hA
  set B : TrioSeq := shiftr01 2 0 Y' with hB
  have hBlen : B.length = Y'.length := by rw [hB]; exact shiftr01_length 2 0 Y'
  have econt : ((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 Y' = A ++ B := by rw [hA, hB]; rfl
  rw [econt]
  have hAl : A.length = 1 := by rw [hA]; rfl
  have hidx : (A ++ B).length - 1 = A.length + (Y'.length - 1) := by
    rw [List.length_append, hBlen, hAl]; omega
  rw [hidx]
  refine noParent_ctx (A := A) (B := B) (b := Y'.length - 1) (j := j) ?_ ?_ ?_ ?_
  · rw [hBlen]; omega
  · intro k hk _
    have hk0 : k = 0 := by rw [hA] at hk; simp at hk; omega
    subst hk0
    show j ≤ entry A 1 0
    rw [hA]; show j ≤ u + 1; omega
  · rw [hB, entry1_shiftr01, hj_eq]
  · rw [hB, hasParent_shiftr01]; exact hY'orph

/-- **(B) GRAFT j≤v at level u**. Inlined from Graft61C (verified green). -/
theorem childLoadC_graft_le {v u jj : ℕ} (hu : v ≤ u) (hjv : jj ≤ v) (hj1 : 1 ≤ jj)
    {Y : TrioSeq} (hYne : Y ≠ [])
    (hYj : entry Y 1 (Y.length - 1) = jj) (hY2 : entry Y 2 (Y.length - 1) = 0)
    (hYorph : ¬ hasParent Y 1 (Y.length - 1))
    (hzK : ∀ z ∈ Wg (2 * jj - 1), based z →
      GTC CQ u (((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 (mlift (graft Y z) v (u - v)))) :
    GTC CQ u (((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 (mlift Y v (u - v))) := by
  have hYl : 0 < Y.length := List.length_pos_iff.mpr hYne
  set hh : ℕ := entry Y 0 (Y.length - 1) with hhh
  have hcone_no : ¬ coneV Y v (Y.length - 1) := by
    intro hc; have := hc (Y.length - 1) Relation.ReflTransGen.refl; rw [hYj] at this; omega
  have hsrY : srow Y (Y.length - 1) = 1 := by
    unfold srow; rw [hY2, if_neg (by omega), hYj, if_pos (by omega)]
  have hmlen : (mlift Y v (u - v)).length = Y.length := mlift_length Y v (u - v)
  have hmne : mlift Y v (u - v) ≠ [] := by
    intro h; rw [h] at hmlen; simp at hmlen; omega
  have hmj : entry (mlift Y v (u - v)) 1 ((mlift Y v (u - v)).length - 1) = jj := by
    rw [hmlen, entry1_mlift (by omega), if_neg hcone_no, hYj, Nat.add_zero]
  have hm2 : entry (mlift Y v (u - v)) 2 ((mlift Y v (u - v)).length - 1) = 0 := by
    rw [hmlen, entry2_mlift, hY2]
  have hsrm : srow (mlift Y v (u - v)) ((mlift Y v (u - v)).length - 1) = 1 := by
    unfold srow; rw [hm2, if_neg (by omega), hmj, if_pos (by omega)]
  have hmorph : ¬ hasParent (mlift Y v (u - v)) 1 ((mlift Y v (u - v)).length - 1) := by
    intro hp
    have hiff := hasParent_mlift_iff (U := Y) v (u - v) hYne
    rw [hsrY, hsrm] at hiff
    exact hYorph (hiff.mp hp)
  have hgl : Y.getLast hYne = ((hh, jj, 0) : ℕ × ℕ × ℕ) := by
    have h1 : Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) = Y.getLast hYne := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
        List.getLast_eq_getElem]
      rfl
    rw [← h1, getD_eq_entries, ← hhh, hYj, hY2]
  have hYsplit : Y = Y.dropLast ++ [((hh, jj, 0) : ℕ × ℕ × ℕ)] := by
    rw [← hgl]; exact (List.dropLast_append_getLast hYne).symm
  have hlowtie : ∀ i, i < ([((hh, jj, 0) : ℕ × ℕ × ℕ)]).length →
      ∃ k, Relation.ReflTransGen (nextrel0 [((hh, jj, 0) : ℕ × ℕ × ℕ)]) k i ∧
        entry [((hh, jj, 0) : ℕ × ℕ × ℕ)] 1 k ≤ v := by
    intro i hi; simp only [List.length_singleton] at hi
    obtain rfl : i = 0 := by omega
    exact ⟨0, Relation.ReflTransGen.refl, by show jj ≤ v; omega⟩
  have hmY : mlift Y v (u - v) = mlift Y.dropLast v (u - v) ++ [((hh, jj, 0) : ℕ × ℕ × ℕ)] := by
    conv_lhs => rw [hYsplit]
    exact mlift_append_low hlowtie (u - v)
  set Yd : TrioSeq := mlift Y.dropLast v (u - v) with hYd
  set K' : TrioSeq := ((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 Yd with hK'
  have hcontent : ((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 (mlift Y v (u - v))
      = K' ++ [((hh + 2, jj, 0) : ℕ × ℕ × ℕ)] := by
    rw [hmY, hK', shiftr01_append0]
    simp only [shiftr01, List.map_cons, List.map_nil, List.cons_append, Nat.add_zero]
  rw [hcontent]
  refine GTC_orph (C := CQ) (v := u) (K := K') (h := hh + 2) (j := jj) hj1 (by omega) ?_ ?_
  · have hnc := row1_noCross (u := u) (j := jj) (by omega) hmne hmj hmorph
    rwa [hcontent] at hnc
  · intro z hz hbz
    have hlowz : ∀ i, i < (shiftr01 hh 0 z).length →
        ∃ k, Relation.ReflTransGen (nextrel0 (shiftr01 hh 0 z)) k i ∧
          entry (shiftr01 hh 0 z) 1 k ≤ v :=
      low_of_Wg (j := jj) (Wg_mono (show 2 * jj - 1 ≤ 2 * jj by omega) hz) hh hjv
    have hgz : graft Y z = Y.dropLast ++ shiftr01 hh 0 z := by
      unfold graft; rw [← hhh]; rfl
    have hmgz : mlift (graft Y z) v (u - v) = Yd ++ shiftr01 hh 0 z := by
      rw [hgz, mlift_append_low hlowz (u - v)]
    have hcomm : ((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 (mlift (graft Y z) v (u - v))
        = K' ++ shiftr01 (hh + 2) 0 z := by
      rw [hmgz, hK', shiftr01_append0, shiftr01_add0, List.cons_append]
    have hres := hzK z hz hbz
    rw [hcomm] at hres
    exact hres

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
      · -- SHORT: Y=[(0,0,0)] (len≤1, lev0, based) → content=[(1,u+1,1),(2,0,0)]
        sorry
      · -- OPER: natDom Y. hasParent-last → GTC_oper+oper_shift; else (lev-0 last) → flat
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
        · -- j ≤ v : GTC_orph at level u (via Graft61C.childLoadC_graft_le) — GREEN
          have hjv : jj ≤ v := by omega
          have hYorph : ¬ hasParent Y 1 (Y.length - 1) := by have h := hd.2; rwa [hsrY] at h
          refine childLoadC_graft_le hu hjv hj1 hYne hjj.symm h20 hYorph (fun z hz hbz => ?_)
          have hzm : z ∈ Wg m' := by rwa [show 2 * jj - 1 = m' by omega] at hz
          exact (hgr z hzm hbz).2 (based_graft_arg hYne hb hbz) u hu
        · -- j = v+1 : gtc_tie at level u (cross-level hload via hgr@all-u) — OPEN
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
