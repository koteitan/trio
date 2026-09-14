/-
HeS.lean: 深い葉（同段 q=m）の GTC 版の核 upleaf_deep_coreT。
HeN.upleafT_core（q<m）と HeQ.upleaf_deep_core（q=m, GpT 版）の合成: gtc_oper で深い節点を展開に落とす。
hpM0/hm は呼び出し側が与える（深い葉の悪い根は下位の祖先）。hrep は展開が木なので GoodTTL で出る。
-/
import HeN

namespace TRIO
namespace HeN

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HaG HbD HbM HbP HbS HbU HbV HbX HcA HcI HcM
open HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ HdQ HdR
open HeB HeG HeH HeI HeK HeL HeM

theorem upleaf_deep_coreT {C : ℕ → List TrioSeq → Prop} {u : ℕ} {Y D : TrioSeq} {d q m : ℕ} (hD : Fr D)
    (hm : 1 ≤ m)
    (hpM0 : hasParent (((0, q, 0) : ℕ × ℕ × ℕ) :: (D ++ [((1, m, 0) : ℕ × ℕ × ℕ)]))
      (srow (D ++ [((1, m, 0) : ℕ × ℕ × ℕ)]) ((D ++ [((1, m, 0) : ℕ × ℕ × ℕ)]).length - 1))
      (D ++ [((1, m, 0) : ℕ × ℕ × ℕ)]).length)
    (hrep : ∀ j, GTC C u (Y ++ shiftr01 d 0
      (((1, q, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (HeH.towR q D j)))) :
    GTC C u (Y ++ shiftr01 d 0
      (((1, q, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (D ++ [((1, m, 0) : ℕ × ℕ × ℕ)]))) := by
  obtain ⟨R, hR⟩ : ∃ R : TrioSeq, R = D ++ [((1, m, 0) : ℕ × ℕ × ℕ)] := ⟨_, rfl⟩
  rw [← hR]
  have hRok : argOK R := by
    intro x hx
    rw [hR] at hx
    rcases List.mem_append.mp hx with hx | hx
    · have := hD x hx; omega
    · simp at hx; subst hx; show 0 < 1; omega
  have hRne : R ≠ [] := by simp [hR]
  have hRlen : R.length - 1 = D.length + 0 := by simp [hR]
  have eL : ∀ i, entry R i (R.length - 1) = entry [((1, m, 0) : ℕ × ℕ × ℕ)] i 0 := by
    intro i; rw [hRlen, hR, entry_append_right]
  have e0 : entry R 0 (R.length - 1) = 1 := by rw [eL]; rfl
  have e1 : entry R 1 (R.length - 1) = m := by rw [eL]; rfl
  have e2' : entry R 2 (R.length - 1) = 0 := by rw [eL]; rfl
  have hsr : srow R (R.length - 1) = 1 := by unfold srow; rw [e2', e1]; simp; omega
  have hnpR : ¬ hasParent R 1 (R.length - 1) := by
    rintro ⟨k, hk, -⟩
    have hk' : nextrel1 R k (R.length - 1) := by
      unfold nextR at hk; rwa [if_neg (by omega), if_pos rfl] at hk
    obtain ⟨-, -, hkl, -, hle0, -⟩ := hk'
    have hrec := rtg0_rec hle0.2.2 (R.length - 1) hkl le_rfl
    rw [e0] at hrec
    have hkD : k < D.length := by omega
    rw [hR, Small.entry_append_left hkD] at hrec
    have := getD_row0_ge hD hkD
    omega
  have hd : domT R (2 * m - 1) := by
    refine ⟨?_, ?_⟩
    · unfold lev; rw [e1, e2']; omega
    · rw [hsr]; exact hnpR
  have hRl : 0 < R.length := List.length_pos_iff.mpr hRne
  have hpM : hasParent (((0, q, 0) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length := hR ▸ hpM0
  have hdl : R.dropLast = D := by rw [hR, List.dropLast_concat]
  have htow : ∀ j, shiftr01 1 0 (tow q 0 R (j + 1))
      = ((1, q, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (D ++ shiftr01 1 0 (tow q 0 R j)) := by
    intro j
    rw [tow, graft_eq_shift, e0, hdl]
    simp [shiftr01]
  have htR : ∀ j, D ++ shiftr01 1 0 (tow q 0 R j) = HeH.towR q D j := by
    intro j
    induction j with
    | zero => simp [tow, HeH.towR, shiftr01]
    | succ j ih => rw [htow, ih]; rfl
  have eV : ((1, q, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 R
      = shiftr01 1 0 (((0, q, 0) : ℕ × ℕ × ℕ) :: R) := by simp [shiftr01]
  have hlen2 : 2 ≤ (((0, q, 0) : ℕ × ℕ × ℕ) :: R).length := by simp; omega
  have hpM' : hasParent (((0, q, 0) : ℕ × ℕ × ℕ) :: R)
      (srow (((0, q, 0) : ℕ × ℕ × ℕ) :: R) ((((0, q, 0) : ℕ × ℕ × ℕ) :: R).length - 1))
      ((((0, q, 0) : ℕ × ℕ × ℕ) :: R).length - 1) := by
    have hl : ((((0, q, 0) : ℕ × ℕ × ℕ) :: R).length - 1) = R.length := by simp
    rw [hl, srow_cons_last hRne]; exact hpM
  rw [eV]
  refine HdR.gtc_oper (by rw [shiftr01_length]; exact hlen2)
    (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpM') (fun m' hm' => ?_)
  have eO := oper_shift [] (((0, q, 0) : ℕ × ℕ × ℕ) :: R) 1 m' hlen2 hpM'
  simp only [List.nil_append] at eO
  rw [eO, oper_cons_tower1 hRok hRne hd hsr hpM]
  obtain ⟨j, rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
  rw [htow, htR]
  exact hrep j

/-- ★ HeQ.upleaf_deep_core の GTC 版（一般の R、tstep_oper → gtc_oper）。展開は tow q 0 R。 -/
theorem upleaf_deep_coreT_gen {C : ℕ → List TrioSeq → Prop} {u d q : ℕ} {Y R : TrioSeq}
    (hRok : argOK R) (hRne : R ≠ [])
    (hd_ : domT R (2 * entry R 1 (R.length - 1) - 1))
    (hsr : srow R (R.length - 1) = 1)
    (hpM : hasParent (((0, q, 0) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length)
    (hrep : ∀ m', 1 ≤ m' → GTC C u
      (Y ++ shiftr01 d 0 (shiftr01 1 0 (tow q 0 R m')))) :
    GTC C u (Y ++ shiftr01 d 0 (shiftr01 1 0 (((0, q, 0) : ℕ × ℕ × ℕ) :: R))) := by
  have hRl : 0 < R.length := List.length_pos_iff.mpr hRne
  have hlen2 : 2 ≤ (((0, q, 0) : ℕ × ℕ × ℕ) :: R).length := by simp; omega
  have hpM' : hasParent (((0, q, 0) : ℕ × ℕ × ℕ) :: R)
      (srow (((0, q, 0) : ℕ × ℕ × ℕ) :: R) ((((0, q, 0) : ℕ × ℕ × ℕ) :: R).length - 1))
      ((((0, q, 0) : ℕ × ℕ × ℕ) :: R).length - 1) := by
    have hl : ((((0, q, 0) : ℕ × ℕ × ℕ) :: R).length - 1) = R.length := by simp
    rw [hl, srow_cons_last hRne]; exact hpM
  refine HdR.gtc_oper (U := shiftr01 1 0 (((0, q, 0) : ℕ × ℕ × ℕ) :: R)) (d := d)
    (by rw [shiftr01_length]; exact hlen2)
    (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpM') (fun m' hm' => ?_)
  have eO := oper_shift [] (((0, q, 0) : ℕ × ℕ × ℕ) :: R) 1 m' hlen2 hpM'
  simp only [List.nil_append] at eO
  rw [eO, oper_cons_tower1 hRok hRne hd_ hsr hpM]
  exact hrep m' hm'

/-- ★ HeQ.upleaf_deep_coreD の GTC 版（悪い根 q < m, descent D は row1 ≥ m, 葉の深さ d0）。 -/
theorem upleaf_deep_coreDT {C : ℕ → List TrioSeq → Prop} {u d q d0 m : ℕ} {Y D : TrioSeq}
    (hD : Fr D) (hD1 : ∀ p ∈ D, m ≤ p.2.1) (hd0 : 1 ≤ d0) (hqm : q < m) (hm : 1 ≤ m)
    (hrep : ∀ m', 1 ≤ m' → GTC C u
      (Y ++ shiftr01 d 0 (shiftr01 1 0 (tow q 0 (D ++ [((d0, m, 0) : ℕ × ℕ × ℕ)]) m')))) :
    GTC C u (Y ++ shiftr01 d 0 (shiftr01 1 0
      (((0, q, 0) : ℕ × ℕ × ℕ) :: (D ++ [((d0, m, 0) : ℕ × ℕ × ℕ)])))) := by
  obtain ⟨R, hR⟩ : ∃ R, R = D ++ [((d0, m, 0) : ℕ × ℕ × ℕ)] := ⟨_, rfl⟩
  have hRne : R ≠ [] := by simp [hR]
  have hRlen : R.length - 1 = D.length + 0 := by simp [hR]
  have eL : ∀ i, entry R i (R.length - 1) = entry [((d0, m, 0) : ℕ × ℕ × ℕ)] i 0 := by
    intro i; rw [hRlen, hR, entry_append_right]
  have e0 : entry R 0 (R.length - 1) = d0 := by rw [eL]; rfl
  have e1 : entry R 1 (R.length - 1) = m := by rw [eL]; rfl
  have e2 : entry R 2 (R.length - 1) = 0 := by rw [eL]; rfl
  have hRl : 0 < R.length := List.length_pos_iff.mpr hRne
  have hRok : argOK R := by
    intro x hx; rw [hR] at hx
    rcases List.mem_append.mp hx with hx | hx
    · have := hD x hx; omega
    · simp at hx; subst hx; exact hd0
  have hsr : srow R (R.length - 1) = 1 := by unfold srow; rw [e2, e1]; simp; omega
  have hnpR : ¬ hasParent R 1 (R.length - 1) := by
    rintro ⟨k, hk, -⟩
    have hk' : nextrel1 R k (R.length - 1) := by
      unfold nextR at hk; rwa [if_neg (by omega), if_pos rfl] at hk
    obtain ⟨-, -, hklt, hlt, -, -⟩ := hk'
    rw [e1] at hlt
    have hkD : k < D.length := by rw [hRlen] at hklt; omega
    have hmem : D.getD k (0, 0, 0) ∈ D := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkD]; exact List.getElem_mem hkD
    have : m ≤ entry R 1 k := by
      rw [hR, Small.entry_append_left hkD]; exact hD1 _ hmem
    omega
  have hd_ : domT R (2 * entry R 1 (R.length - 1) - 1) := by
    refine ⟨?_, ?_⟩
    · unfold lev; rw [e1, e2]; omega
    · rw [hsr]; exact hnpR
  have hpM : hasParent (((0, q, 0) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length := by
    rw [hsr]
    refine hasParent_one_of (b := R.length) (k := 0) (by simp) hRl
      ⟨by simp, by simp, rtg0_zero (fun l hl0 hl => ?_) (by simp)⟩ ?_
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      rw [entry_cons]
      have hl' : l' < R.length := by simp at hl; omega
      have hmem : R.getD l' (0, 0, 0) ∈ R := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl']; exact List.getElem_mem hl'
      have := hRok _ hmem
      show 0 < (R.getD l' (0, 0, 0)).1; omega
    · rw [entry_cons_last hRne 1, e1]; show q < m; omega
  rw [← hR] at hrep ⊢
  exact upleaf_deep_coreT_gen hRok hRne hd_ hsr hpM hrep

end HeN
end TRIO
