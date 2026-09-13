/-
GxV.lean: 中身の中の z の字（行 2 の親が頭）の展開と、その字の差し込み口。

    ((0,u,0) :: (P ++ [(h,u+1,1)]))⟦n⟧ = ⋃_{k<n} ((0,u+k,0) :: mlift P u k)↑(k·h)
-/
import GxT

namespace TRIO
namespace GxV

open Wset
open Small
open GwS
open Gw
open GwU
open GwZ
open GxD
open GxG
open GxJ
open GxK
open GxL
open GxN
open GxP
open GxR
open GxT

open Classical in
theorem oper_zcone {u h : ℕ} {P : TrioSeq} (hP : Fr P) (hh : 1 ≤ h)
    (hc : coneV (P ++ [((h, u + 1, 1) : ℕ × ℕ × ℕ)]) u P.length) (n : ℕ) :
    (((0, u, 0) : ℕ × ℕ × ℕ) :: (P ++ [((h, u + 1, 1) : ℕ × ℕ × ℕ)]))⟦n⟧
      = (List.range n).flatMap (fun k =>
          shiftr01 (k * h) 0 (((0, u + k, 0) : ℕ × ℕ × ℕ) :: mlift P u k)) := by
  obtain ⟨A, hA⟩ : ∃ A : TrioSeq, A = P ++ [((h, u + 1, 1) : ℕ × ℕ × ℕ)] := ⟨_, rfl⟩
  rw [← hA] at hc ⊢
  have hAok : argOK A := by
    intro p hp
    rw [hA] at hp
    rcases List.mem_append.mp hp with hp | hp
    · have := hP p hp; omega
    · simp at hp; subst hp; show 0 < h; omega
  have hAl : A.length = P.length + 1 := by rw [hA]; simp
  have eA : ∀ r, entry A r P.length = entry [((h, u + 1, 1) : ℕ × ℕ × ℕ)] r 0 := by
    intro r; rw [hA]; simpa using entry_append_right P [((h, u + 1, 1) : ℕ × ℕ × ℕ)] r 0
  have eM : ∀ r, entry (((0, u, 0) : ℕ × ℕ × ℕ) :: A) r (P.length + 1)
      = entry [((h, u + 1, 1) : ℕ × ℕ × ℕ)] r 0 := by
    intro r; rw [entry_cons, eA]
  have ez0 : entry (((0, u, 0) : ℕ × ℕ × ℕ) :: A) 0 (P.length + 1) = h := by rw [eM]; rfl
  have ez1 : entry (((0, u, 0) : ℕ × ℕ × ℕ) :: A) 1 (P.length + 1) = u + 1 := by rw [eM]; rfl
  have ez2 : entry (((0, u, 0) : ℕ × ℕ × ℕ) :: A) 2 (P.length + 1) = 1 := by rw [eM]; rfl
  have eH : ∀ r, entry (((0, u, 0) : ℕ × ℕ × ℕ) :: A) r 0 = entry [((0, u, 0) : ℕ × ℕ × ℕ)] r 0 := by
    intro r; rfl
  have hle1 : le1 (((0, u, 0) : ℕ × ℕ × ℕ) :: A) 0 (P.length + 1) := by
    have := (le1_cons_iff_coneV (z := 0) hAok (show P.length < A.length by omega)).mpr hc
    rwa [Nat.add_comm 1] at this
  have hn2 : nextrel2 (((0, u, 0) : ℕ × ℕ × ℕ) :: A) 0 (P.length + 1) := by
    refine ⟨by simp, by simp [hAl], by omega, by rw [ez2]; show 0 < 1; omega, hle1, ?_⟩
    rintro j ⟨hj0, hjl⟩
    rcases Relation.ReflTransGen.cases_tail hjl.2.2 with h1 | ⟨c, hc1, hc2⟩
    · rw [h1]
    · exfalso
      obtain ⟨-, -, -, hclt, hle0, -⟩ := hc2
      have hjc := rtg1_index_le hc1
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      have hl0 := (le0_cons _ A c' P.length).mp hle0
      have := hc c' hl0.2.2
      rw [entry_cons, ez1] at hclt
      omega
  have hpar : hasParent (((0, u, 0) : ℕ × ℕ × ℕ) :: A) 2 (P.length + 1) :=
    hasParent2_of_le1_witness (by simp [hAl]) hle1.2.2 (by rw [ez2]; show 0 < 1; omega)
  have hparent : parent (((0, u, 0) : ℕ × ℕ × ℕ) :: A) 2 (P.length + 1) = 0 :=
    hpar.unique (parent_nextR hpar) hn2
  have hsrow : srow (((0, u, 0) : ℕ × ℕ × ℕ) :: A) (P.length + 1) = 2 := by
    unfold srow; rw [ez2]; rfl
  rw [L53.oper_unfold (j1 := P.length + 1) (i1 := 2) (j0 := 0) (d0 := h) (d1 := 1)
      (by simp [hAl]) (by omega) (by rw [ez0, ez1, ez2]; omega) hsrow.symm hpar hparent.symm
      (by rw [if_pos (by omega), ez0]; show h = h - 0; omega)
      (by rw [if_pos (by omega), ez1]; show 1 = u + 1 - u; omega) n]
  simp only [List.take_zero, List.nil_append, Nat.sub_zero]
  apply List.flatMap_congr
  intro k _
  rw [List.range'_succ, List.map_cons]
  have hl00 : le0 (((0, u, 0) : ℕ × ℕ × ℕ) :: A) 0 0 := ⟨by simp, by simp, Relation.ReflTransGen.refl⟩
  have hl11 : le1 (((0, u, 0) : ℕ × ℕ × ℕ) :: A) 0 0 := ⟨by simp, by simp, Relation.ReflTransGen.refl⟩
  simp only [shiftr01, List.map_cons]
  congr 1
  · rw [if_pos hl00, if_pos hl11]
    show ((0 + k * h, u + k * 1, 0) : ℕ × ℕ × ℕ) = ((0 + k * h, u + k + 0, 0) : ℕ × ℕ × ℕ)
    simp
  · unfold mlift
    rw [List.range'_eq_map_range, List.map_map, List.map_map]
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp_apply]
    have hiA : i < A.length := by omega
    have eP : ∀ r, entry (((0, u, 0) : ℕ × ℕ × ℕ) :: A) r (1 + i) = entry P r i := by
      intro r
      rw [Nat.add_comm 1 i, entry_cons, hA, Small.entry_append_left hi]
    rw [eP, eP, eP, if_pos (by rw [Nat.add_comm 1 i]; exact le0_cons_zero hAok i hiA)]
    have hiff : le1 (((0, u, 0) : ℕ × ℕ × ℕ) :: A) 0 (1 + i) ↔ coneV P u i := by
      rw [le1_cons_iff_coneV hAok hiA, hA, coneV_append_left hi]
    by_cases hci : coneV P u i
    · rw [if_pos (hiff.mpr hci), if_pos hci] <;> simp
    · rw [if_neg (fun h' => hci (hiff.mp h')), if_neg hci] <;> simp

#print axioms oper_zcone


theorem oper_zcone_succ {u h : ℕ} {P : TrioSeq} (hP : Fr P) (hh : 1 ≤ h)
    (hc : coneV (P ++ [((h, u + 1, 1) : ℕ × ℕ × ℕ)]) u P.length) (n : ℕ) :
    (((0, u, 0) : ℕ × ℕ × ℕ) :: (P ++ [((h, u + 1, 1) : ℕ × ℕ × ℕ)]))⟦n + 1⟧
      = ((0, u, 0) : ℕ × ℕ × ℕ) :: (P ++ shiftr01 h 0
          ((((0, u + 1, 0) : ℕ × ℕ × ℕ) :: (mlift P u 1 ++ [((h, u + 1 + 1, 1) : ℕ × ℕ × ℕ)]))⟦n⟧)) := by
  have hc' : coneV (mlift P u 1 ++ [((h, u + 1 + 1, 1) : ℕ × ℕ × ℕ)]) (u + 1) (mlift P u 1).length := by
    rw [mlift_length]
    have := coneV_mlift (by simp) hc 1
    rw [mlift_snoc_cone P _ hc 1] at this
    exact this
  rw [oper_zcone hP hh hc (n + 1), oper_zcone (Fr_mlift hP u 1) hh hc' n, List.range_succ_eq_map,
    List.flatMap_cons, List.flatMap_map, GwV.shiftr01_flatMap]
  have e0 : shiftr01 (0 * h) 0 (((0, u + 0, 0) : ℕ × ℕ × ℕ) :: mlift P u 0)
      = ((0, u, 0) : ℕ × ℕ × ℕ) :: P := by
    rw [Nat.zero_mul, shiftr01_zero', mlift_zero, Nat.add_zero]
  rw [e0, List.cons_append]
  congr 2
  apply List.flatMap_congr
  intro k _
  simp only [Nat.succ_eq_add_one]
  rw [shiftr01_add0, mlift_mlift, Nat.add_mul, Nat.one_mul, Nat.add_comm 1 k,
    show u + 1 + k = u + (k + 1) by omega]

#print axioms oper_zcone_succ


/-! ## 1 段だけの中身の閉包 -/

/-- 段 u だけで、どの語 L の後にも中身 K の字を足せる。 -/
def GT1 (u : ℕ) (K : TrioSeq) : Prop :=
  ∀ L : List TrioSeq, (∀ X ∈ L, ∀ x ∈ X, 1 ≤ x.1) → BwT u L → rword 0 u (L ++ [K]) ∈ Wstarv u

theorem GT1_of_GT {u : ℕ} {K : TrioSeq} (h : GT u K) : GT1 u K := by
  intro L hL hB
  have := h L hL hB u le_rfl
  rw [Nat.sub_self] at this
  simpa only [mlift_zero, List.map_id'] using this

theorem GT1_of_GTall {u : ℕ} {K : TrioSeq} (h : GTall u K) : GT1 u K := GT1_of_GT (GT_of_GTall h)

theorem GT1_oper {v : ℕ} {K : TrioSeq} (hlen : 2 ≤ K.length)
    (hp : hasParent K (srow K (K.length - 1)) (K.length - 1))
    (hIH : ∀ n, 1 ≤ n → GT1 v (K⟦n⟧)) : GT1 v K := by
  intro L hL hB _ a ha
  rw [rword0_snoc]
  refine A1g_intro (Or.inr (Or.inl ⟨natDom_append_shift _ _ 1
    (by intro h; rw [h] at hlen; simp at hlen) hp, fun n hn => ?_⟩))
  rw [oper_shift _ _ 1 n hlen hp]
  have h := hIH n hn L hL hB (argOK_rword v _) a ha
  rw [rword0_snoc] at h
  exact h

theorem GT1_orph {v : ℕ} {K : TrioSeq} {h j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ v)
    (hnp : ¬ hasParent (K ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1
      ((K ++ [((h, j, 0) : ℕ × ℕ × ℕ)]).length - 1))
    (hzK : ∀ z ∈ Wg (2 * j - 1), based z → GT1 v (K ++ shiftr01 h 0 z)) :
    GT1 v (K ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
  intro L hL hB _ a ha
  rw [rword0_snoc]
  obtain ⟨P, hP⟩ : ∃ P : TrioSeq,
      P = (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v L) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)] := ⟨_, rfl⟩
  obtain ⟨hPlen, hP0, hPL1, hPL0, hPmid⟩ := P_facts v L
  rw [← hP] at hPlen hP0 hPL1 hPL0 hPmid ⊢
  have hnp' := noParent_letter (P := P) (T := K ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) (v := v) (j := j)
    (by omega) hPlen hP0 hPL1 hPL0 hPmid (by simp)
    (by
      rw [show (K ++ [((h, j, 0) : ℕ × ℕ × ℕ)]).length - 1 = K.length + 0 by simp,
        entry_append_right]
      rfl) hnp
  have eS : shiftr01 1 0 (K ++ [((h, j, 0) : ℕ × ℕ × ℕ)])
      = shiftr01 1 0 K ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)] := by
    rw [shiftr01_append0, shift_col]
  have hidx : P.length + ((K ++ [((h, j, 0) : ℕ × ℕ × ℕ)]).length - 1)
      = (P ++ shiftr01 1 0 K).length := by simp [shiftr01]
  rw [eS, hidx, ← List.append_assoc] at hnp'
  rw [eS, ← List.append_assoc]
  have hLL : ((P ++ shiftr01 1 0 K) ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)]).length - 1
      = (P ++ shiftr01 1 0 K).length := by simp
  have eL : ∀ r, entry ((P ++ shiftr01 1 0 K) ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)]) r
      (P ++ shiftr01 1 0 K).length = entry [((h + 1, j, 0) : ℕ × ℕ × ℕ)] r 0 := by
    intro r
    simpa using entry_append_right (P ++ shiftr01 1 0 K) [((h + 1, j, 0) : ℕ × ℕ × ℕ)] r 0
  have e1 : entry [((h + 1, j, 0) : ℕ × ℕ × ℕ)] 1 0 = j := rfl
  have e2 : entry [((h + 1, j, 0) : ℕ × ℕ × ℕ)] 2 0 = 0 := rfl
  have e0 : entry [((h + 1, j, 0) : ℕ × ℕ × ℕ)] 0 0 = h + 1 := rfl
  have hsr : srow ((P ++ shiftr01 1 0 K) ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)])
      (P ++ shiftr01 1 0 K).length = 1 := by
    unfold srow; rw [eL, eL, e2, e1]; simp; omega
  have hdom : domT ((P ++ shiftr01 1 0 K) ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)]) (2 * j - 1) := by
    refine ⟨?_, ?_⟩
    · unfold lev; rw [hLL, eL, eL, e1, e2]; omega
    · rw [hLL, hsr]; exact hnp'
  refine A1g_intro (Or.inr (Or.inr ⟨2 * j - 1, by omega, hdom, by rw [hLL, eL, e2],
    fun z hz hbz => ?_⟩))
  have hg : graft ((P ++ shiftr01 1 0 K) ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)]) z
      = P ++ shiftr01 1 0 (K ++ shiftr01 h 0 z) := by
    rw [graft_eq_shift, List.dropLast_concat, hLL, eL, e0, shiftr01_append0, shiftr01_add0,
      List.append_assoc]
  rw [hg, hP, ← rword0_snoc]
  exact hzK z hz hbz L hL hB (argOK_rword v _) a ha

#print axioms GT1_orph

theorem GT1_tie {v : ℕ} {K : TrioSeq} {x : ℕ}
    (hcone : coneV (K ++ [((x, v + 1, 0) : ℕ × ℕ × ℕ)]) v K.length)
    (hload : ∀ Z ∈ Wg (2 * v + 1), based Z → GT1 v (K ++ shiftr01 x 0 Z)) :
    GT1 v (K ++ [((x, v + 1, 0) : ℕ × ℕ × ℕ)]) := by
  intro L hL hB _ a ha
  obtain ⟨P, hP⟩ : ∃ P : TrioSeq, P = rword 0 v L ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)] := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : TrioSeq, R = P ++ shiftr01 1 0 (K ++ [((x, v + 1, 0) : ℕ × ℕ × ℕ)]) :=
    ⟨_, rfl⟩
  have eM : ((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v (L ++ [K ++ [((x, v + 1, 0) : ℕ × ℕ × ℕ)]])
      = ((0, v, 0) : ℕ × ℕ × ℕ) :: R := by
    rw [rword0_snoc, hR, hP]; rfl
  have hRw : R = rword 0 v (L ++ [K ++ [((x, v + 1, 0) : ℕ × ℕ × ℕ)]]) := by
    have := eM; simp only [List.cons.injEq, true_and] at this; exact this.symm
  have hRok : argOK R := by rw [hRw]; exact argOK_rword v _
  have hRne : R ≠ [] := by simp [hR, hP]
  have eRX : R = (P ++ shiftr01 1 0 K) ++ [((x + 1, v + 1, 0) : ℕ × ℕ × ℕ)] := by
    rw [hR, shiftr01_append0, shift_col, List.append_assoc]
  have hRlen : R.length - 1 = (P ++ shiftr01 1 0 K).length := by rw [eRX]; simp
  have eL : ∀ r, entry R r (R.length - 1) = entry [((x + 1, v + 1, 0) : ℕ × ℕ × ℕ)] r 0 := by
    intro r
    rw [hRlen]
    rw [eRX]
    simpa using entry_append_right (P ++ shiftr01 1 0 K) [((x + 1, v + 1, 0) : ℕ × ℕ × ℕ)] r 0
  have e0 : entry R 0 (R.length - 1) = x + 1 := by rw [eL]; rfl
  have e1 : entry R 1 (R.length - 1) = v + 1 := by rw [eL]; rfl
  have e2 : entry R 2 (R.length - 1) = 0 := by rw [eL]; rfl
  have hsr : srow R (R.length - 1) = 1 := by unfold srow; rw [e2, e1]; simp
  have hPlen : 1 ≤ P.length := by simp [hP]
  have hPL : P.length - 1 = (rword 0 v L).length + 0 := by simp [hP]
  have hPL1 : entry P 1 (P.length - 1) = v + 1 := by rw [hPL, hP, entry_append_right]; rfl
  have hPL0 : entry P 0 (P.length - 1) = 1 := by rw [hPL, hP, entry_append_right]; rfl
  have hPmid : ∀ k, k < P.length - 1 → 1 ≤ entry P 0 k := by
    intro k hk
    rw [hPL] at hk
    rw [hP, Small.entry_append_left (by omega)]
    have hmem : (rword 0 v L).getD k (0, 0, 0) ∈ rword 0 v L := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact List.getElem_mem _
    have := rword_ge 0 v L _ hmem
    show 1 ≤ ((rword 0 v L).getD k (0, 0, 0)).1
    omega
  have hnpK : ¬ hasParent (K ++ [((x, v + 1, 0) : ℕ × ℕ × ℕ)]) 1 K.length :=
    noParent_of_coneV hcone (by
      rw [show K.length = K.length + 0 from rfl, entry_append_right]
      show v + 1 ≤ v + 1; exact le_rfl)
  have hnpT : ¬ hasParent (K ++ [((x, v + 1, 0) : ℕ × ℕ × ℕ)]) 1
      ((K ++ [((x, v + 1, 0) : ℕ × ℕ × ℕ)]).length - 1) := by
    simpa using hnpK
  have hnpR : ¬ hasParent R 1 (R.length - 1) := by
    have h := noParent_head (P := P) (T := K ++ [((x, v + 1, 0) : ℕ × ℕ × ℕ)]) (v := v)
      (j := v + 1) le_rfl hPlen hPL1 hPL0 hPmid (by simp)
      (by rw [show (K ++ [((x, v + 1, 0) : ℕ × ℕ × ℕ)]).length - 1 = K.length + 0 by simp,
        entry_append_right]; rfl) hnpT
    have hidx : R.length - 1 = P.length + ((K ++ [((x, v + 1, 0) : ℕ × ℕ × ℕ)]).length - 1) := by
      rw [hR]; simp [shiftr01]
    rw [hidx]
    rw [hR]
    exact h
  have hd : domT R (2 * v + 1) := by
    refine ⟨?_, ?_⟩
    · unfold lev; rw [e1, e2]; omega
    · rw [hsr]; exact hnpR
  have hRl : 0 < R.length := List.length_pos_iff.mpr hRne
  have hpM : hasParent (((0, v, 0) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length := by
    rw [hsr]
    refine hasParent_one_of (b := R.length) (k := 0) (by simp) hRl
      ⟨by simp, by simp, rtg0_zero (fun l hl0 hl => ?_) (by simp)⟩ ?_
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      rw [entry_cons]
      have hl' : l' < R.length := by simp at hl; omega
      have hmem : R.getD l' (0, 0, 0) ∈ R := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl']; exact List.getElem_mem hl'
      have := hRok _ hmem
      show 0 < (R.getD l' (0, 0, 0)).1
      omega
    · rw [entry_cons_last hRne 1, e1]; show v < v + 1; omega
  have hnat : natDom (((0, v, 0) : ℕ × ℕ × ℕ) :: R) := by
    refine natDom_iff.mpr (Or.inr ?_)
    have hl : ((((0, v, 0) : ℕ × ℕ × ℕ) :: R).length - 1) = R.length := by simp
    rw [hl, srow_cons_last hRne]
    exact hpM
  have hdl : R.dropLast = P ++ shiftr01 1 0 K := by rw [eRX, List.dropLast_concat]
  have htow : ∀ k, tow v 0 R k ∈ Wg (2 * v) := by
    intro k
    induction k with
    | zero => simpa [tow] using Wg_nil (2 * v)
    | succ k ih =>
        have e : tow v 0 R (k + 1) = ((0, v, 0) : ℕ × ℕ × ℕ) ::
            rword 0 v (L ++ [K ++ shiftr01 x 0 (tow v 0 R k)]) := by
          rw [tow, graft_eq_shift, e0, hdl, rword0_snoc, shiftr01_append0, shiftr01_add0, hP]
          simp [List.append_assoc]
        rw [e]
        exact hload (tow v 0 R k) (Wg_mono (by omega) ih) (based_tow v 0 R k) L hL hB
          (argOK_rword v _) (2 * v) le_rfl
  rw [eM]
  refine A1g_intro (Or.inr (Or.inl ⟨hnat, fun n _ => ?_⟩))
  rw [oper_cons_tower1 hRok hRne hd hsr hpM]
  exact Wg_mono ha (htow n)

#print axioms GT1_tie

end GxV
end TRIO
