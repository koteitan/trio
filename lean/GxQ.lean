/-
GxQ.lean: tools/gen_gxq.py が生成。タイ・2 段上の錐・荷の中身を持つシート行。
-/
import GxP

namespace TRIO
namespace GxQ

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP

/-- ★ シート行 780。 -/
theorem R780_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 782。 -/
theorem R782_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 783。 -/
theorem R783_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 784。 -/
theorem R784_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 0), (2, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_nil 1)) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 785。 -/
theorem R785_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_nil 1) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 786。 -/
theorem R786_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 0), (2, 2, 1), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_load (u := 1) (TF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 787。 -/
theorem R787_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_nil 1)) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 788。 -/
theorem R788_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_nil 1)) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_consT (v := 2) (TF_tie (u := 2) (TF_nil 2) (GTF_nil 2)) (WordsG_nil 2)))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 789。 -/
theorem R789_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_nil 1)) (WordsG_consT (v := 1) (TF_nil 1) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 790。 -/
theorem R790_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_tie (u := 1) (GTF_nil 1) (GTF_nil 1))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 793。 -/
theorem R793_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_nil 1))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 794。 -/
theorem R794_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_nil 1))) (WordsG_nil 1)))) rfl) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_nil 1))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 795。 -/
theorem R795_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_nil 1))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 796。 -/
theorem R796_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_nil 1))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 797。 -/
theorem R797_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (2, 1, 0), (3, 2, 1), (4, 2, 0), (5, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_nil 1))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_nil 1))) (WordsG_nil 1)))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 798。 -/
theorem R798_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (2, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_nil 1))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 799。 -/
theorem R799_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 4, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_nil 1))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_consT (v := 2) (TF_tie (u := 2) (TF_nil 2) (GTF_h (u := 2) (GTF_nil 2) (GHF_nil 2))) (WordsG_nil 2)))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 800。 -/
theorem R800_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 4, 0), (3, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_nil 1))) (WordsG_nil 1))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 2) (WordsG_consT (v := 2) (TF_tie (u := 2) (TF_nil 2) (GTF_h (u := 2) (GTF_nil 2) (GHF_nil 2))) (WordsG_nil 2))) (Wg_of_starOK (starOK_wordsG (v := 3) (WordsG_nil 3))) rfl)) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 801。 -/
theorem R801_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 802。 -/
theorem R802_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_nil 1))) (WordsG_consT (v := 1) (TF_nil 1) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 803。 -/
theorem R803_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (2, 2, 1), (2, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_nil 1))) (WordsG_consT (v := 1) (TF_nil 1) (WordsG_nil 1)))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 804。 -/
theorem R804_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 805。 -/
theorem R805_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_load (u := 0) (TF_nil 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 806。 -/
theorem R806_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_nil 0)) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 807。 -/
theorem R807_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (2, 2, 1), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_nil 0)) (WordsG_nil 0)))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_nil 1))) (WordsG_consT (v := 1) (TF_load (u := 1) (TF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 808。 -/
theorem R808_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (2, 2, 1), (3, 1, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_nil 0)) (WordsG_nil 0)))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_nil 1))) (WordsG_consT (v := 1) (TF_load (u := 1) (TF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (WordsG_consT (v := 1) (TF_nil 1) (WordsG_nil 1)))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 809。 -/
theorem R809_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (2, 2, 1), (3, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_nil 0)) (WordsG_nil 0)))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_nil 1))) (WordsG_consT (v := 1) (TF_load (u := 1) (TF_load (u := 1) (TF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 810。 -/
theorem R810_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (2, 2, 1), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_nil 0)) (WordsG_nil 0)))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_nil 1))) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_nil 1)) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 811。 -/
theorem R811_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_nil 0)) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 812。 -/
theorem R812_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_nil 0)) (GTF_nil 0)) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 813。 -/
theorem R813_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_nil 0)) (GTF_nil 0)) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 814。 -/
theorem R814_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (3, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_load (u := 0) (GTF_nil 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl)) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 815。 -/
theorem R815_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_tie (u := 0) (GTF_nil 0) (GTF_nil 0))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 816。 -/
theorem R816_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_tie (u := 0) (GTF_nil 0) (GTF_nil 0))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 817。 -/
theorem R817_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_tie (u := 0) (GTF_nil 0) (GTF_tie (u := 0) (GTF_nil 0) (GTF_nil 0)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 818。 -/
theorem R818_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 819。 -/
theorem R819_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 820。 -/
theorem R820_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 821。 -/
theorem R821_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_load (u := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 822。 -/
theorem R822_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (GTF_nil 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 823。 -/
theorem R823_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (GTF_nil 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_nil 1))) (GTF_nil 1)) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 824。 -/
theorem R824_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (GTF_nil 0)) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 825。 -/
theorem R825_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (GTF_nil 0)) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (GTF_nil 0)) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 826。 -/
theorem R826_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (GTF_nil 0)) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (GTF_nil 0)) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 827。 -/
theorem R827_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (2, 1, 0), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_load (u := 0) (TF_tie (u := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (GTF_nil 0)) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 828。 -/
theorem R828_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (2, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_tie (u := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (GTF_nil 0)) (GTF_nil 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 829。 -/
theorem R829_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_tie (u := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (GTF_nil 0)) (GTF_nil 0)) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 830。 -/
theorem R830_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (2, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (GTF_tie (u := 0) (GTF_nil 0) (GTF_nil 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 831。 -/
theorem R831_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 832。 -/
theorem R832_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_tie (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0)) (GTF_nil 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 833。 -/
theorem R833_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (3, 1, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_tie (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0)) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 834。 -/
theorem R834_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0)) (GHF_nil 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 835。 -/
theorem R835_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (3, 2, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0)) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 836。 -/
theorem R836_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0)) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 837。 -/
theorem R837_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0)) (GHF_nil 0))) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0)) (GHF_nil 0))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 838。 -/
theorem R838_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (3, 2, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0)) (GHF_nil 0))) (GTF_nil 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 839。 -/
theorem R839_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (3, 2, 0), (2, 1, 0), (3, 2, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0)) (GHF_nil 0))) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0)) (GHF_nil 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 840。 -/
theorem R840_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (3, 2, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_tie (u := 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0)) (GHF_nil 0)) (GTF_nil 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 841。 -/
theorem R841_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (3, 2, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0)) (GHF_nil 0)) (GHF_nil 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 842。 -/
theorem R842_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (3, 2, 0), (3, 2, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0)) (GHF_nil 0)) (GHF_nil 0)) (GHF_nil 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 843。 -/
theorem R843_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_load (u := 0) (GHF_nil 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 844。 -/
theorem R844_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 0, 0), (5, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_load (u := 0) (GHF_nil 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))) (by omega)) rfl))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 845。 -/
theorem R845_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 846。 -/
theorem R846_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_load (u := 1) (GHF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 847。 -/
theorem R847_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (5, 1, 0), (2, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_load (u := 1) (GHF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 848。 -/
theorem R848_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (5, 1, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_load (u := 1) (GHF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl))) (WordsG_consT (v := 1) (TF_nil 1) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 849。 -/
theorem R849_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (5, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_load (u := 1) (GHF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl))) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_load (u := 1) (GHF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl))) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 850。 -/
theorem R850_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (5, 1, 0), (3, 2, 0), (4, 3, 0), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_load (u := 1) (GHF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl))) (GTF_h (u := 1) (GTF_nil 1) (GHF_load (u := 1) (GHF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 851。 -/
theorem R851_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (5, 1, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_load (u := 1) (GHF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)) (GHF_nil 1))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 852。 -/
theorem R852_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (5, 1, 0), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_load (u := 1) (GHF_load (u := 1) (GHF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 853。 -/
theorem R853_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (5, 1, 0), (6, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_load (u := 1) (GHF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_nil 1) (WordsG_nil 1)))) (by omega)) rfl))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 854。 -/
theorem R854_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_tie (u := 1) (GHF_nil 1) (GTF_nil 1)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 855。 -/
theorem R855_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (5, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 4, 0), (6, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_tie (u := 1) (GHF_nil 1) (GTF_nil 1)))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_consT (v := 2) (TF_tie (u := 2) (TF_nil 2) (GTF_h (u := 2) (GTF_nil 2) (GHF_tie (u := 2) (GHF_nil 2) (GTF_nil 2)))) (WordsG_nil 2)))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 856。 -/
theorem R856_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 857。 -/
theorem R857_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (1, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 858。 -/
theorem R858_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 859。 -/
theorem R859_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 860。 -/
theorem R860_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 861。 -/
theorem R861_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (GTF_nil 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 862。 -/
theorem R862_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (2, 1, 0), (3, 2, 0), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 863。 -/
theorem R863_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (3, 1, 0), (4, 2, 0), (5, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_tie (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0))) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 864。 -/
theorem R864_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0))) (GHF_nil 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 865。 -/
theorem R865_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (3, 2, 0), (4, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0))) (GHF_load (u := 0) (GHF_nil 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 866。 -/
theorem R866_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (3, 2, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0))) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 867。 -/
theorem R867_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (3, 2, 0), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0))) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 868。 -/
theorem R868_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (4, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_load (u := 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 869。 -/
theorem R869_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)) (GTF_nil 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 870。 -/
theorem R870_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)) (GTF_nil 0)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 871。 -/
theorem R871_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_tie (u := 0) (GTF_nil 0) (GTF_nil 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 872。 -/
theorem R872_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (5, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_tie (u := 0) (GTF_nil 0) (GTF_nil 0))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 873。 -/
theorem R873_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (5, 1, 0), (6, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_tie (u := 0) (GTF_nil 0) (GTF_tie (u := 0) (GTF_nil 0) (GTF_nil 0)))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 874。 -/
theorem R874_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 875。 -/
theorem R875_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (5, 2, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))) (GTF_nil 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 876。 -/
theorem R876_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (5, 2, 0), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_tie (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0)) (GTF_nil 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 877。 -/
theorem R877_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (5, 2, 0), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0)) (GHF_nil 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 878。 -/
theorem R878_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (5, 2, 0), (6, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_load (u := 0) (GHF_nil 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 879。 -/
theorem R879_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (5, 2, 0), (6, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 880。 -/
theorem R880_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (5, 2, 0), (6, 1, 0), (7, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_tie (u := 0) (GTF_nil 0) (GTF_nil 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 881。 -/
theorem R881_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 1, 0), (5, 2, 0), (6, 1, 0), (7, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

#print axioms R780_mem
#print axioms R881_mem

end GxQ
end TRIO
