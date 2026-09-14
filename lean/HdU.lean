/-
HdU.lean: 最上段の最後の語で、F のタイの子の木 us のあとに 2 段上の節点 (2, v+2, 0) を置いた形（シート行 1647）。

    K = wLT v (Uss ++ [us], []) ++ [(2, v+2, 0)] = P ++ ((0, v+1, 0) :: R)↑1、R = topTs v us ++ [(1, v+2, 0)]
    K⟦j+1⟧ = P ++ (tow (v+1) 0 R (j+1))↑1 = F のタイの子の木 T_j（T_0 = us、T_{j+1} = us ++ [tie T_j]）（GxP.GTs_C2 の写し）
  木なので HdS.GoodTT_all で良く、GTC_oper で閉じる。
-/
import HdS

namespace TRIO
namespace HdU

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HaG HbD HbM HbP HbS HbU HbV HbX HcA HcI HcM
open HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ HdL HdM HdN HdO HdP HdQ HdR HdS

/-- ★ F のタイの子の木のあとに 2 段上の節点。 -/
theorem GTC_N2 {v : ℕ} {Uss : List (List UT)} (hU : ∀ us ∈ Uss, TRaws v us) {us : List UT}
    (hus : TRaws v us) :
    GTC CLT v (wLT v (Uss ++ [us], []) ++ [((2, v + 2, 0) : ℕ × ℕ × ℕ)]) := by
  obtain ⟨D, hD⟩ : ∃ D, D = topTs v us := ⟨_, rfl⟩
  have hDF : Fr D := by rw [hD]; exact Fr_topTs v us
  obtain ⟨R, hR⟩ : ∃ R : TrioSeq, R = D ++ [((1, v + 2, 0) : ℕ × ℕ × ℕ)] := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = FTL0 (v + 1) (Uss.map (topTs v)) := ⟨_, rfl⟩
  have eK : wLT v (Uss ++ [us], []) ++ [((2, v + 2, 0) : ℕ × ℕ × ℕ)]
      = P ++ shiftr01 1 0 (((0, v + 1, 0) : ℕ × ℕ × ℕ) :: R) := by
    rw [hP, hR, hD]; simp [wLT, FTL0_snoc, unitsC, shiftr01]
  rw [eK]
  have hRok : argOK R := by
    intro p hp
    rw [hR] at hp
    rcases List.mem_append.mp hp with hp | hp
    · have := hDF p hp; omega
    · simp at hp; subst hp; show 0 < 1; omega
  have hRne : R ≠ [] := by simp [hR]
  have hRlen : R.length - 1 = D.length + 0 := by simp [hR]
  have eL : ∀ r, entry R r (R.length - 1) = entry [((1, v + 2, 0) : ℕ × ℕ × ℕ)] r 0 := by
    intro r; rw [hRlen, hR, entry_append_right]
  have e0 : entry R 0 (R.length - 1) = 1 := by rw [eL]; rfl
  have e1 : entry R 1 (R.length - 1) = v + 2 := by rw [eL]; rfl
  have e2' : entry R 2 (R.length - 1) = 0 := by rw [eL]; rfl
  have hsr : srow R (R.length - 1) = 1 := by unfold srow; rw [e2', e1]; simp
  have hnpR : ¬ hasParent R 1 (R.length - 1) := by
    rintro ⟨k, hk, -⟩
    have hk' : nextrel1 R k (R.length - 1) := by
      unfold nextR at hk; rwa [if_neg (by omega), if_pos rfl] at hk
    obtain ⟨-, -, hkl, -, hle0, -⟩ := hk'
    have hrec := rtg0_rec hle0.2.2 (R.length - 1) hkl le_rfl
    rw [e0] at hrec
    have hkD : k < D.length := by omega
    rw [hR, Small.entry_append_left hkD] at hrec
    have := getD_row0_ge hDF hkD
    omega
  have hd : domT R (2 * (v + 1) + 1) := by
    refine ⟨?_, ?_⟩
    · unfold lev; rw [e1, e2']; omega
    · rw [hsr]; exact hnpR
  have hRl : 0 < R.length := List.length_pos_iff.mpr hRne
  have hpM : hasParent (((0, v + 1, 0) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length := by
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
    · rw [entry_cons_last hRne 1, e1]; show v + 1 < v + 2; omega
  have hdl : R.dropLast = D := by rw [hR, List.dropLast_concat]
  have htow : ∀ j, shiftr01 1 0 (tow (v + 1) 0 R (j + 1))
      = ((1, v + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (D ++ shiftr01 1 0 (tow (v + 1) 0 R j)) := by
    intro j
    rw [tow, graft_eq_shift, e0, hdl]
    simp [shiftr01]
  have hT : ∀ j, ∃ T : List UT, TRaws v T ∧ topTs v T = D ++ shiftr01 1 0 (tow (v + 1) 0 R j) := by
    intro j
    induction j with
    | zero => exact ⟨us, hus, by simp [tow, shiftr01, hD]⟩
    | succ j ih =>
        obtain ⟨T, hTr, hTe⟩ := ih
        refine ⟨us ++ [UT.tie T], TRaws_snoc.mpr ⟨hus, hTr⟩, ?_⟩
        rw [topTs_append, htow, ← hTe, hD]
        simp [topTs, topT]
  have hlen2 : 2 ≤ (((0, v + 1, 0) : ℕ × ℕ × ℕ) :: R).length := by simp; omega
  have hpM' : hasParent (((0, v + 1, 0) : ℕ × ℕ × ℕ) :: R)
      (srow (((0, v + 1, 0) : ℕ × ℕ × ℕ) :: R) ((((0, v + 1, 0) : ℕ × ℕ × ℕ) :: R).length - 1))
      ((((0, v + 1, 0) : ℕ × ℕ × ℕ) :: R).length - 1) := by
    have hl : ((((0, v + 1, 0) : ℕ × ℕ × ℕ) :: R).length - 1) = R.length := by simp
    rw [hl, srow_cons_last hRne]; exact hpM
  refine gtc_oper (Y := P) (d := 1) hlen2 hpM' (fun m hm => ?_)
  rw [oper_cons_tower1 hRok hRne hd hsr hpM]
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [htow]
  obtain ⟨T, hTr, hTe⟩ := hT j
  have hG := GoodTT_all (v := v) (Uss ++ [T]) (fun us' h' => by
    rcases List.mem_append.mp h' with h' | h'
    · exact hU us' h'
    · simp at h'; subst h'; exact hTr) v le_rfl
  have eW : wLT v (Uss ++ [T], [])
      = P ++ ((1, v + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (D ++ shiftr01 1 0 (tow (v + 1) 0 R j)) := by
    rw [hP, ← hTe]; simp [wLT, FTL0_snoc, unitsC]
  rwa [eW] at hG

/-- ★ 語の並び（CLT）のあとに最後の語 K。 -/
theorem starOK_lastT {v : ℕ} (ps : List (List (List UT) × List (Option TrioSeq))) (h : PsLT v ps)
    {K : TrioSeq} (hK : GTC CLT v K) (hKF : ∀ x ∈ K, 1 ≤ x.1) :
    StarOK v (rword 0 v (ps.map (wLT v) ++ [K])) := by
  refine ⟨?_, fun p hp => rword_ge 0 v _ p hp⟩
  have hB := hK _ ⟨ps, h, rfl⟩ (Fr_CLT v ps) (BwT_CLT v ps h) v le_rfl
  simpa only [Nat.sub_self, mlift_zero, List.map_id'] using hB

/-- ★ シート行 1647。 -/
theorem R1647_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have hK := GTC_N2 (v := 0) (Uss := []) (fun _ h => by simp at h) (us := []) trivial
  have hKF : ∀ x ∈ wLT 0 ([] ++ [[]], []) ++ [((2, 0 + 2, 0) : ℕ × ℕ × ℕ)], 1 ≤ x.1 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Fr_wLT 0 _ x hx
    · simp at hx; subst hx; show 1 ≤ 2; omega
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_lastT (v := 0) [] (PsLT_nil 0) hK hKF))
  simpa [shiftr01, rword, rcol, wLT, HbP.FTL0, topTs, topT, unitsC] using h

end HdU
end TRIO
