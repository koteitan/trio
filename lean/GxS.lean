/-
GxS.lean: tools/gen_gxq.py が生成。タイ・2 段上の錐・荷の中身を持つシート行。
-/
import GxR

namespace TRIO
namespace GxS

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR

/-- ★ シート行 882。 -/
theorem R882_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 883。 -/
theorem R883_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 884。 -/
theorem R884_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0)))) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0)))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 885。 -/
theorem R885_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0)))) (GTF_nil 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 886。 -/
theorem R886_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (2, 1, 0), (3, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0)))) (GTF_h (u := 0) (GTF_nil 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 887。 -/
theorem R887_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_tie (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0))) (GTF_nil 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 888。 -/
theorem R888_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0))) (GHF_nil 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 889。 -/
theorem R889_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (3, 2, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0))) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 890。 -/
theorem R890_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (3, 2, 0), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0))) (GHF_tie (u := 0) (GHF_nil 0) (GTF_nil 0)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 891。 -/
theorem R891_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (3, 2, 0), (4, 1, 0), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0))) (GHF_tie (u := 0) (GHF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 892。 -/
theorem R892_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (3, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0))) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 893。 -/
theorem R893_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (3, 2, 0), (4, 2, 0), (3, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0))) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0))) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 894。 -/
theorem R894_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (4, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_load (u := 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0)) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 895。 -/
theorem R895_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0)) (GTF_nil 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 896。 -/
theorem R896_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0)) (GTF_nil 0)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 897。 -/
theorem R897_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (4, 1, 0), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0)) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 898。 -/
theorem R898_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (4, 1, 0), (5, 2, 0), (6, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0)) (GTF_h (u := 0) (GTF_nil 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 899。 -/
theorem R899_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_hh (u := 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0)) (GHHF_nil 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 900。 -/
theorem R900_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (4, 2, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_tie (u := 0) (GHF_hh (u := 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0)) (GHHF_nil 0)) (GTF_nil 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 901。 -/
theorem R901_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (4, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_hh (u := 0) (GHF_hh (u := 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_nil 0)) (GHHF_nil 0)) (GHHF_nil 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 902。 -/
theorem R902_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (5, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_load (u := 0) (GHHF_nil 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 903。 -/
theorem R903_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_tie (u := 0) (GHHF_nil 0) (GTF_nil 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 904。 -/
theorem R904_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (5, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (5, 3, 0), (6, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_tie (u := 0) (GHHF_nil 0) (GTF_nil 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tie (u := 1) (TF_nil 1) (GTF_h (u := 1) (GTF_nil 1) (GHF_hh (u := 1) (GHF_nil 1) (GHHF_tie (u := 1) (GHHF_nil 1) (GTF_nil 1))))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 905。 -/
theorem R905_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (5, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_tie (u := 0) (GHHF_nil 0) (GTF_nil 0))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 906。 -/
theorem R906_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (5, 1, 0), (6, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tie (u := 0) (TF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_hh (u := 0) (GHF_nil 0) (GHHF_tie (u := 0) (GHHF_nil 0) (GTF_h (u := 0) (GTF_nil 0) (GHF_nil 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

#print axioms R882_mem
#print axioms R906_mem

end GxS
end TRIO
