/-
HdK.lean: 最上段の最後の語で、F のタイの子の最後の F の位置のタイに flat の子 (3, 0, 0) を付けた形（シート行 1641）。

    K = wLU v (Uss ++ [us ++ [none]], []) ++ [(3, 0, 0)]
    K⟦n⟧ = wLU v (Uss ++ [us ++ none^n], [])（oper_snoc00''）なので GTC_oper と HcS.GoodTU_all で出る。
-/
import HcS

namespace TRIO
namespace HdK

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HbD HbM HbP HbQ HbR HbS HbT HbU HbV HbX HcI HcJ HcM HcN HcP HcS

theorem unitsC_rep_none (v : ℕ) (us : List (Option TrioSeq)) : ∀ n,
    unitsC v (us ++ List.replicate n none) = unitsC v us ++ List.replicate n ((1, v + 1, 0) : ℕ × ℕ × ℕ)
  | 0 => by simp
  | n + 1 => by
      rw [List.replicate_succ', ← List.append_assoc, unitsC_snoc, unitsC_rep_none v us n,
        List.replicate_succ']
      simp [unitC]

theorem range_flatMap_single (c : ℕ × ℕ × ℕ) : ∀ n,
    (List.range n).flatMap (fun _ => [c]) = List.replicate n c
  | 0 => by simp
  | n + 1 => by
      rw [List.range_succ, List.flatMap_append, range_flatMap_single c n, List.replicate_succ']
      simp

/-- ★ 最後の F の位置のタイに flat の子。 -/
theorem GTC_noneFlat {v : ℕ} {Uss : List (List (Option TrioSeq))} (hU : ∀ us ∈ Uss, RawU v us)
    {us : List (Option TrioSeq)} (hus : RawU v us) :
    GTC CLU v (wLU v (Uss ++ [us ++ [none]], []) ++ [((3, 0, 0) : ℕ × ℕ × ℕ)]) := by
  obtain ⟨Y0, hY0⟩ : ∃ Y0, Y0 = FTL0 (v + 1) ((Uss ++ [us]).map (unitsC v)) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : TrioSeq, M = [((2, v + 1, 0) : ℕ × ℕ × ℕ)] := ⟨_, rfl⟩
  have e : wLU v (Uss ++ [us ++ [none]], []) = Y0 ++ M := by
    rw [hY0, hM]; simp [wLU, FTL0_snoc, unitsC_snoc, unitC, unitsC, shiftr01]
  have eN : ∀ n, wLU v (Uss ++ [us ++ List.replicate n none], [])
      = Y0 ++ (List.range n).flatMap (fun _ => M) := by
    intro n
    rw [hM, range_flatMap_single, hY0]
    simp only [wLU, List.map_append, List.map_singleton, FTL0_snoc, unitsC_rep_none]
    simp [unitsC, shiftr01]
  rw [e]
  have hMne : M ≠ [] := by rw [hM]; simp
  have hMpos : 0 < M.length := List.length_pos_iff.mpr hMne
  have hhead : entry M 0 0 < 3 := by rw [hM]; show 2 < 3; omega
  have htail : ∀ r', 1 ≤ r' → r' < M.length → 3 ≤ entry M 0 r' := by
    intro r' hr1 hr2; rw [hM] at hr2; simp at hr2; omega
  have hlast : hasParent (M ++ [((3, 0, 0) : ℕ × ℕ × ℕ)])
      (srow (M ++ [((3, 0, 0) : ℕ × ℕ × ℕ)]) ((M ++ [((3, 0, 0) : ℕ × ℕ × ℕ)]).length - 1))
      ((M ++ [((3, 0, 0) : ℕ × ℕ × ℕ)]).length - 1) := by
    have hidx : (M ++ [((3, 0, 0) : ℕ × ℕ × ℕ)]).length - 1 = M.length + 0 := by simp
    rw [hidx, srow_append_right]
    have hs : srow [((3, 0, 0) : ℕ × ℕ × ℕ)] 0 = 0 := rfl
    rw [hs]
    refine (hasParent_zero_iff (by simp)).mpr ⟨0, by omega, ?_⟩
    rw [Small.entry_append_left hMpos, entry_append_right]
    exact hhead
  refine GTC_oper ?_ ?_ (fun n _ => ?_)
  · simp only [List.length_append, List.length_singleton]; omega
  · have hidx : (Y0 ++ M ++ [((3, 0, 0) : ℕ × ℕ × ℕ)]).length - 1
        = Y0.length + ((M ++ [((3, 0, 0) : ℕ × ℕ × ℕ)]).length - 1) := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [hidx, List.append_assoc, srow_append_right]
    exact hasParent_append_right_of _ _ hlast
  · rw [oper_snoc00'' Y0 hMne hhead htail n, ← eN n]
    have hR : ∀ us' ∈ Uss ++ [us ++ List.replicate n none], RawU v us' := by
      intro us' h'
      rcases List.mem_append.mp h' with h' | h'
      · exact hU us' h'
      · rw [List.mem_singleton] at h'; rw [h']
        intro Z hZ
        rcases List.mem_append.mp hZ with hZ | hZ
        · exact hus Z hZ
        · simp at hZ
    exact GoodTU_all _ hR v le_rfl

/-- ★ 語の並び（CLU）のあとに最後の語 K。 -/
theorem starOK_last {v : ℕ} (ps : List (List (List (Option TrioSeq)) × List (Option TrioSeq)))
    (h : PsLU v ps) {K : TrioSeq} (hK : GTC CLU v K) (hKF : ∀ x ∈ K, 1 ≤ x.1) :
    StarOK v (rword 0 v (ps.map (wLU v) ++ [K])) := by
  refine ⟨?_, fun p hp => rword_ge 0 v _ p hp⟩
  have hL : ∀ X ∈ ps.map (wLU v), ∀ x ∈ X, 1 ≤ x.1 := Fr_CLU v ps
  have hB := hK _ ⟨ps, h, rfl⟩ hL (BwT_CLU v ps h) v le_rfl
  simpa only [Nat.sub_self, mlift_zero, List.map_id'] using hB

theorem Fr_noneFlat (v : ℕ) (Uss : List (List (Option TrioSeq))) (us : List (Option TrioSeq)) :
    ∀ x ∈ wLU v (Uss ++ [us ++ [none]], []) ++ [((3, 0, 0) : ℕ × ℕ × ℕ)], 1 ≤ x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact Fr_wLU v _ x hx
  · simp at hx; subst hx; show 1 ≤ 3; omega

/-- ★ シート行 1641。 -/
theorem R1641_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (4, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_last (v := 0) [] (PsLU_nil 0)
    (GTC_noneFlat (Uss := []) (HcS.RawUs_nil 0) (us := []) (RawU_nil 0)) (Fr_noneFlat 0 [] [])))
  simpa [shiftr01, rword, rcol, wLU, FTL0, unitsC, unitC] using h

end HdK
end TRIO
