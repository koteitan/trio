/-
HdT.lean: F のタイの子に入れ子の F の位置のタイを持つ語のシート行（HdS.starOK_CLT）。
-/
import HdS

namespace TRIO
namespace HdT

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GzJ HdA HdQ HdS

/-- ★ シート行 1642。 -/
theorem R1642_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CLT (v := 0)
    [([[UT.tie 0 [UT.tie 0 []]]], ([] : List (Option TrioSeq)))]
    (PsLT_cons (fun us hus => by simp at hus; subst hus; simp [TRaws, TRaw]) (by simp [NoTie]) (RawU_nil 0)
      (PsLT_nil 0)) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, wLT, HbP.FTL0, topTs, topT, unitsC] using h

/-- ★ シート行 1643。 -/
theorem R1643_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CLT (v := 0)
    [([[UT.tie 0 [UT.tie 0 []]]], ([] : List (Option TrioSeq)))]
    (PsLT_cons (fun us hus => by simp at hus; subst hus; simp [TRaws, TRaw]) (by simp [NoTie]) (RawU_nil 0)
      (PsLT_nil 0)) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, wLT, HbP.FTL0, topTs, topT, unitsC] using h

/-- ★ シート行 1644。 -/
theorem R1644_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CLT (v := 0)
    [([[UT.tie 0 [UT.tie 0 []]]], ([] : List (Option TrioSeq))), ([], [])]
    (PsLT_cons (fun us hus => by simp at hus; subst hus; simp [TRaws, TRaw]) (by simp [NoTie]) (RawU_nil 0)
      (PsLT_cons (fun us hus => by simp at hus) (by simp [NoTie]) (RawU_nil 0) (PsLT_nil 0)))
    (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, wLT, HbP.FTL0, topTs, topT, unitsC] using h

/-- ★ シート行 1645。 -/
theorem R1645_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (4, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CLT (v := 0)
    [([[UT.tie 0 [UT.tie 0 [], UT.tie 0 []]]], ([] : List (Option TrioSeq))), ([], [])]
    (PsLT_cons (fun us hus => by simp at hus; subst hus; simp [TRaws, TRaw]) (by simp [NoTie]) (RawU_nil 0)
      (PsLT_cons (fun us hus => by simp at hus) (by simp [NoTie]) (RawU_nil 0) (PsLT_nil 0)))
    (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, wLT, HbP.FTL0, topTs, topT, unitsC] using h

/-- ★ シート行 1646。 -/
theorem R1646_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (5, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CLT (v := 0)
    [([[UT.tie 0 [UT.tie 0 [UT.tie 0 []]]]], ([] : List (Option TrioSeq))), ([], [])]
    (PsLT_cons (fun us hus => by simp at hus; subst hus; simp [TRaws, TRaw]) (by simp [NoTie]) (RawU_nil 0)
      (PsLT_cons (fun us hus => by simp at hus) (by simp [NoTie]) (RawU_nil 0) (PsLT_nil 0)))
    (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, wLT, HbP.FTL0, topTs, topT, unitsC] using h

end HdT
end TRIO
