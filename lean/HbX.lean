/-
HbX.lean: 最上段の最後の遠い語で、最後の F のタイの子の末尾が F の位置の子のないタイ（行 1583〜1614 の形）。

    語 FTL0 (v+1) (Ds ++ [D]) ++ [(2, v+1, 0)]      （Ds, D は荷だけの子。末尾の (2, v+1, 0) が F の位置のタイ）
- GTC CL v（その語）: GTC_tie（x = 2）。タイの展開の荷 Z は最後の F のタイの子の荷になり、HbV.GoodT_Ds で出る。
- 後ろには TF の語だけ（BwT_append_words）。
-/
import HbV

namespace TRIO
namespace HbX

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HbD HbM HbP HbQ HbR HbS HbT HbU HbV

/-- FTL0 の列で行 0 が 1 以下の列（字と F のタイ）は、行 1 が r。 -/
theorem FTL0_low_row1 (r : ℕ) : ∀ (Ds : List TrioSeq), (∀ D ∈ Ds, Fr D) →
    ∀ y, y < (FTL0 r Ds).length → entry (FTL0 r Ds) 0 y ≤ 1 → entry (FTL0 r Ds) 1 y = r := by
  intro Ds
  induction Ds using List.reverseRecOn with
  | nil =>
      intro _ y hy _
      have hy0 : y = 0 := by
        simp only [FTL0, List.flatMap_nil, List.length_cons, List.length_nil] at hy; omega
      subst hy0; rfl
  | append_singleton Ds D ih =>
      intro hFr y hy h0
      have hFrD : Fr D := hFr D (List.mem_append_right _ (List.mem_singleton_self _))
      have ih' := ih (fun D' h' => hFr D' (List.mem_append_left _ h'))
      rw [FTL0_snoc] at hy h0 ⊢
      rcases Nat.lt_or_ge y (FTL0 r Ds).length with hlt | hge
      · rw [Small.entry_append_left hlt] at h0 ⊢
        exact ih' y hlt h0
      · obtain ⟨w, rfl⟩ : ∃ w, y = (FTL0 r Ds).length + w := ⟨y - (FTL0 r Ds).length, by omega⟩
        rw [entry_append_right] at h0 ⊢
        rcases w with _ | w
        · rfl
        · exfalso
          rw [entry_cons] at h0
          have hw : w < D.length := by
            simp only [List.length_append, List.length_cons, shiftr01_length] at hy; omega
          rw [entry0_shiftr01 hw] at h0
          have := getD_row0_ge hFrD hw
          omega

theorem coneV_Fleaf {v : ℕ} {Ds : List TrioSeq} (hFr : ∀ D ∈ Ds, Fr D) :
    coneV (FTL0 (v + 1) Ds ++ [((2, v + 1, 0) : ℕ × ℕ × ℕ)]) v (FTL0 (v + 1) Ds).length := by
  intro y hy
  have hyle := rtg0_le hy
  rcases Nat.lt_or_ge y (FTL0 (v + 1) Ds).length with hlt | hge
  · have hrec := rtg0_rec hy (FTL0 (v + 1) Ds).length hlt le_rfl
    rw [Small.entry_append_left hlt, show (FTL0 (v + 1) Ds).length = (FTL0 (v + 1) Ds).length + 0 from rfl,
      entry_append_right] at hrec
    have e2 : entry [((2, v + 1, 0) : ℕ × ℕ × ℕ)] 0 0 = 2 := rfl
    rw [e2] at hrec
    rw [Small.entry_append_left hlt, FTL0_low_row1 (v + 1) Ds hFr y hlt (by omega)]
    omega
  · have hy' : y = (FTL0 (v + 1) Ds).length := by simp at hyle; omega
    subst hy'
    rw [show (FTL0 (v + 1) Ds).length = (FTL0 (v + 1) Ds).length + 0 from rfl, entry_append_right]
    show v < v + 1; omega

/-- ★ 最後の F のタイの子の末尾に F の位置の子のないタイ。 -/
theorem GTC_Fleaf {v : ℕ} {Ds : List TrioSeq} (hDs : DsOK v Ds) {D : TrioSeq} (hD : LoadSeq v D) :
    GTC CL v (FTL0 (v + 1) (Ds ++ [D]) ++ [((2, v + 1, 0) : ℕ × ℕ × ℕ)]) := by
  have hDs' : DsOK v (Ds ++ [D]) := fun D' h' => by
    rcases List.mem_append.mp h' with h' | h'
    · exact hDs D' h'
    · rw [List.mem_singleton] at h'; rw [h']; exact hD
  refine GTC_tie (C := CL) (coneV_Fleaf (fun D' h' => (LoadSeq_fr (hDs' D' h')).1))
    (fun u hu Z hZ hbZ => ?_) (fun L hC u hu => CL_lift L v hC u hu)
  rw [mlift_FTL0 (show v < v + 1 by omega) (u - v) _ (fun D' h' => LoadSeq_fr (hDs' D' h')),
    show v + 1 + (u - v) = u + 1 by omega]
  have hLS : LoadSeq u (D ++ shiftr01 1 0 Z) := LoadSeq_snoc (LoadSeq_mono hu hD) hZ hbZ
  have hDsu : DsOK u (Ds ++ [D ++ shiftr01 1 0 Z]) := fun D' h' => by
    rcases List.mem_append.mp h' with h' | h'
    · exact LoadSeq_mono hu (hDs D' h')
    · rw [List.mem_singleton] at h'; rw [h']; exact hLS
  have hG := GoodT_Ds _ hDsu u le_rfl
  have e : wL u (Ds ++ [D ++ shiftr01 1 0 Z], []) = FTL0 (u + 1) (Ds ++ [D]) ++ shiftr01 2 0 Z := by
    simp [wL, FTL0_snoc, unitsC, shiftr01, Function.comp_def, Nat.add_assoc]
  rwa [e] at hG

theorem BwT_CLF (v : ℕ) (ps : List (List TrioSeq × List (Option TrioSeq))) (h : PsL v ps)
    {Ds : List TrioSeq} (hDs : DsOK v Ds) {D : TrioSeq} (hD : LoadSeq v D) :
    BwT v (ps.map (wL v) ++ [FTL0 (v + 1) (Ds ++ [D]) ++ [((2, v + 1, 0) : ℕ × ℕ × ℕ)]]) :=
  GTC_Fleaf hDs hD _ ⟨ps, h, rfl⟩ (Fr_CL v ps) (BwT_CL v ps h)

theorem Fr_CLF (v : ℕ) (ps : List (List TrioSeq × List (Option TrioSeq))) (Ds : List TrioSeq)
    (D : TrioSeq) :
    ∀ X ∈ ps.map (wL v) ++ [FTL0 (v + 1) (Ds ++ [D]) ++ [((2, v + 1, 0) : ℕ × ℕ × ℕ)]],
      ∀ x ∈ X, 1 ≤ x.1 := by
  intro X hX
  rcases List.mem_append.mp hX with hX | hX
  · exact Fr_CL v ps X hX
  · rw [List.mem_singleton] at hX
    subst hX
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Fr_FTL0 _ _ x hx
    · simp at hx; subst hx; show 1 ≤ 2; omega

/-- ★ 荷の子の語の並び、F の位置のタイで終わる語、TF の語の並び。 -/
theorem starOK_CLF {v : ℕ} (ps : List (List TrioSeq × List (Option TrioSeq))) (h : PsL v ps)
    (Ds : List TrioSeq) (hDs : DsOK v Ds) (D : TrioSeq) (hD : LoadSeq v D) {Ls : List TrioSeq}
    (hW : WordsG v Ls) :
    StarOK v (rword 0 v (ps.map (wL v) ++
      [FTL0 (v + 1) (Ds ++ [D]) ++ [((2, v + 1, 0) : ℕ × ℕ × ℕ)]] ++ Ls)) := by
  refine ⟨?_, fun p hp => rword_ge 0 v _ p hp⟩
  have hB := BwT_append_words (Fr_CLF v ps Ds D) (BwT_CLF v ps h hDs hD) Ls hW v le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

end HbX
end TRIO
