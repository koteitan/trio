/-
HeT.lean: 初の深い葉 — 証明中行 (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,2,0)(4,2,0) ∈ W 0。
深い鎖 tie 1 [tie 1 []] の F のタイの子を upleaf_deep_coreDT（q=1）で展開し、展開が木（dtree）なので
GTC_wLTL で潰す。tow_dtree: tow 1 0 R (j+1) = (0,1,0)::topTs [dtree j]。
-/
import HeS

namespace TRIO
namespace HeT

open Wset Small HdA HdB HdE HdQ HeI HeK HeL
open GwS GxL GxJ GzJ GxP GxN HbP
open HeN

noncomputable def dtree : ℕ → HdA.UT
  | 0 => HdA.UT.tie 1 []
  | j+1 => HdA.UT.tie 1 [HdA.UT.tie 0 [dtree j]]

theorem tow_dtree (j : ℕ) : (tow 1 0 [((1,2,0):ℕ×ℕ×ℕ),((2,2,0):ℕ×ℕ×ℕ)] (j+1) : TrioSeq)
    = ((0,1,0):ℕ×ℕ×ℕ) :: topTs 0 [dtree j] := by
  induction j with
  | zero => simp [dtree, tow, graft_eq_shift, topTs, topT, shiftr01, entry, List.getD]
  | succ j ih =>
    rw [tow, graft_eq_shift]
    simp only [show [((1,2,0):ℕ×ℕ×ℕ),((2,2,0):ℕ×ℕ×ℕ)].dropLast = [((1,2,0):ℕ×ℕ×ℕ)] from rfl,
      show entry [((1,2,0):ℕ×ℕ×ℕ),((2,2,0):ℕ×ℕ×ℕ)] 0 ([((1,2,0):ℕ×ℕ×ℕ),((2,2,0):ℕ×ℕ×ℕ)].length - 1) = 2 from rfl]
    rw [ih]
    simp only [dtree, topTs, topT, shiftr01, List.map_cons, List.map_nil, List.append_nil,
      List.cons_append, List.nil_append, Nat.add_zero, Nat.zero_add, List.map_map]
    refine congrArg (List.cons _) (congrArg (List.cons _) (congrArg (List.cons _) ?_))
    apply List.map_congr_left
    intro p _; refine Prod.ext ?_ (Prod.ext rfl rfl); simp [Function.comp_apply]

theorem TreeTs_dtree (j : ℕ) : TreeTs 0 0 true [dtree j] := by
  induction j with
  | zero => exact TreeTs_cons_up (l := 0) rfl (by decide) (TreeTs_nil 0 1 false) (TreeTs_nil 0 0 true)
  | succ j ih =>
    exact TreeTs_cons_up (l := 0) rfl (by decide)
      (TreeTs_cons_tie0 ih (TreeTs_nil 0 1 false)) (TreeTs_nil 0 0 true)

theorem hK_pm : GTC CLTL 0 (wLT 0 ([[HdA.UT.tie 1 [HdA.UT.tie 1 []]]], ([] : List (Option TrioSeq)))) := by
  have e : wLT 0 ([[HdA.UT.tie 1 [HdA.UT.tie 1 []]]], ([] : List (Option TrioSeq)))
      = ([(1,1,1)] : TrioSeq) ++ shiftr01 0 0 (shiftr01 1 0
        (((0, 1, 0) : ℕ×ℕ×ℕ) :: ([((1,2,0):ℕ×ℕ×ℕ)] ++ [((2, 2, 0) : ℕ×ℕ×ℕ)]))) := by
    simp [wLT, FTL0, topTs, topT, unitsC, shiftr01]
  rw [e]
  refine upleaf_deep_coreDT (C := CLTL) (u := 0) (d := 0) (q := 1) (d0 := 2) (m := 2)
    (D := [(1,2,0)]) (by intro p hp; simp at hp; subst hp; decide) (by intro p hp; simp at hp; subst hp; decide)
    (by decide) (by decide) (by decide) (fun m' hm' => ?_)
  obtain ⟨j, rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
  have ee : ([(1,1,1)] : TrioSeq) ++ shiftr01 0 0 (shiftr01 1 0
      (tow 1 0 ([((1,2,0):ℕ×ℕ×ℕ)] ++ [((2,2,0):ℕ×ℕ×ℕ)]) (j+1)))
      = wLT 0 ([[dtree j]], ([] : List (Option TrioSeq))) := by
    rw [show ([((1,2,0):ℕ×ℕ×ℕ)] ++ [((2,2,0):ℕ×ℕ×ℕ)]) = [((1,2,0):ℕ×ℕ×ℕ),((2,2,0):ℕ×ℕ×ℕ)] from rfl,
      tow_dtree]
    simp [wLT, FTL0, topTs, topT, unitsC, shiftr01]
  rw [ee]
  exact GTC_wLTL (fun us' hus' => by simp at hus'; subst hus'; exact TreeTs_dtree j)
    (GoodTTL_all _ (fun us' hus' => by simp at hus'; subst hus'; exact TreeTs_dtree j))
    [] (by simp [GzJ.NoTie]) (RawU_nil 0)

theorem R_pm : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have hB := hK_pm [] ⟨[], PsLTL_nil 0, rfl⟩ (by simp) (BwT_nil 0)
  have hS : StarOK 0 (rword 0 0 [wLT 0 ([[HdA.UT.tie 1 [HdA.UT.tie 1 []]]], ([] : List (Option TrioSeq)))]) := by
    refine ⟨?_, fun p hp => rword_ge 0 0 _ p hp⟩
    have h2 := hB 0 le_rfl
    rw [Nat.sub_self] at h2
    simpa only [mlift_zero, List.map_id', List.nil_append] using h2
  have h := W0_of_starOK hS
  simpa [rword, rcol, wLT, FTL0, topTs, topT, unitsC, shiftr01] using h

/-- 深い葉の語 K のあと、遠い語の並び Ls を足す（深い葉 + 後ろの遠い語）。 -/
theorem deepleaf1_words {Ls : List TrioSeq} (hW : WordsG 0 Ls) :
    (((0, 0, 0) : ℕ×ℕ×ℕ) :: rword 0 0
      ([wLT 0 ([[HdA.UT.tie 1 [HdA.UT.tie 1 []]]], ([] : List (Option TrioSeq)))] ++ Ls)) ∈ W 0 := by
  have hBK : BwT 0 [wLT 0 ([[HdA.UT.tie 1 [HdA.UT.tie 1 []]]], ([] : List (Option TrioSeq)))] := by
    have := hK_pm [] ⟨[], PsLTL_nil 0, rfl⟩ (by simp) (BwT_nil 0)
    simpa using this
  have hB2 := BwT_append_words (v := 0)
    (L := [wLT 0 ([[HdA.UT.tie 1 [HdA.UT.tie 1 []]]], ([] : List (Option TrioSeq)))])
    (by intro X hX; simp only [List.mem_singleton] at hX; subst hX; exact Fr_wLT 0 _)
    hBK Ls hW
  refine W0_of_starOK ⟨?_, fun p hp => rword_ge 0 0 _ p hp⟩
  have := hB2 0 le_rfl
  rw [Nat.sub_self] at this
  simpa only [mlift_zero, List.map_id', List.map_cons, List.map_nil] using this

/-- ★ シート行 (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,2,0)(4,2,0)(1,1,1)。 -/
theorem R_pm2 : ([(0,0,0),(1,1,1),(2,1,1),(2,1,0),(3,2,0),(4,2,0),(1,1,1)] : TrioSeq) ∈ W 0 := by
  have h := deepleaf1_words (Ls := [([] : TrioSeq)]) (WordsG_consT (TF_nil 0) (WordsG_nil 0))
  simpa [rword, rcol, wLT, FTL0, topTs, topT, unitsC, shiftr01] using h

end HeT
end TRIO
